{-# LANGUAGE OverloadedStrings #-}
-- | Concrete specialization of checked first-order type templates. The source
-- inventory is retained; generated identities carry explicit origin/arguments.
module Agda2SysML.Specialize
  ( Result(..), Instance(..), Type(..), prepare, typeKey, typeValue, signature
  , Signature(..), ArgumentSlot(..), IndexExpr(..), LevelAtom(..), LevelExpr(..), ParameterKind(..), substitute, readType, constrainLevel, levelSymbols, typeAlias, nativeParameters, nativeFamilies ) where

import Agda2SysML.Inventory hiding (prepare, field)
import Agda2SysML.Diagnostic
import qualified Agda2SysML.Reduction as Reduction
import qualified Agda2SysML.UnusedParameters as UnusedParameters
import Agda2SysML.Sharing (digest)
import Control.Monad (forM, forM_, unless, when, foldM, (>=>))
import Control.Monad.Except
import Control.Monad.State.Strict (State, runState, gets, modify')
import Data.Aeson hiding (Result)
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger, floatingOrInteger)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

-- Template variables can be substituted; open-schema levels are rigid names
-- in the caller's scope and must survive a callee's static substitution.
data LevelAtom = BoundLevel Int | RigidLevel Int deriving (Eq,Ord,Show)
data LevelExpr = LevelExpr Integer (M.Map LevelAtom Integer) deriving (Eq,Ord,Show)
data Type = Unused | Parameter Int | Open Int LevelExpr | Named Text [Type] | Level LevelExpr
  | Callable [Type] Type
  | SchemaValue [Type] LevelExpr | SelectedFamily Type
  | FamilyParameter Int [Type] LevelExpr | OpenFamily Int [Type] LevelExpr | FamilyApplication Type [Type]
  | FamilyExpression Type Int Type LevelExpr
  | Runtime Type IndexExpr deriving (Eq,Ord,Show)
-- Runtime positions are absolute within a value telescope. Static arguments
-- on proper projections are retained until those declarations are cloned.
data IndexExpr = IndexInput Int | IndexCaptured Int | IndexLocal Int | IndexConstructor Text [Type] [IndexExpr]
  | IndexNatural Integer | IndexSuccessor IndexExpr | IndexArgument Int | IndexApply IndexExpr IndexExpr
  | IndexTyped Type IndexExpr | IndexFamilyArgument Int
  | IndexLambda [Int] Type IndexExpr
  | IndexProject Text [Type] IndexExpr | IndexCall Text [Type] [IndexExpr] deriving (Eq,Ord,Show)

-- Type evidence for a callable reference is retained while abstracting free
-- context under a family binder. Re-reading a checked type is idempotent.
typedIndex :: Type -> IndexExpr -> IndexExpr
typedIndex ty (IndexTyped _ x) = typedIndex ty x
typedIndex ty x = IndexTyped ty x

-- Closure binders share the hygienic local namespace with type-family binders,
-- never the enclosing runtime telescope or a callback's contract arguments.
bindIndexLocals :: [(Int,IndexExpr)] -> IndexExpr -> IndexExpr
bindIndexLocals bindings = go
  where
    go original@(IndexLocal i) = maybe original id (lookup i bindings)
    go (IndexLambda slots ty x) = IndexLambda slots (mapIndices go ty)
      (bindIndexLocals [(i,value) | (i,value) <- bindings,i `notElem` slots] x)
    go (IndexTyped ty x) = typedIndex (mapIndices go ty) (go x)
    go (IndexApply f x) = IndexApply (go f) (go x)
    go (IndexConstructor c ts xs) = IndexConstructor c (map (mapIndices go) ts) (map go xs)
    go (IndexCall f ts xs) = IndexCall f (map (mapIndices go) ts) (map go xs)
    go (IndexProject f ts x) = IndexProject f (map (mapIndices go) ts) (go x)
    go (IndexSuccessor x) = IndexSuccessor (go x)
    go x = x

-- A carrier/helper identity abstracts runtime values in its static arguments.
-- The captured values become an explicit, ordered telescope prefix; repeated
-- references share one slot. Closed fibres retain their concrete identity.
mapIndices :: (IndexExpr -> IndexExpr) -> Type -> Type
mapIndices f (Callable a b) = Callable (map (mapIndices f) a) (mapIndices f b)
mapIndices f (SchemaValue ds l) = SchemaValue (map (mapIndices f) ds) l
mapIndices f (SelectedFamily value) = SelectedFamily (mapIndices f value)
mapIndices f (Named s xs) = Named s (map (mapIndices f) xs)
mapIndices f (Runtime ty ix) = Runtime (mapIndices f ty) (f ix)
mapIndices f (FamilyApplication ty xs) = FamilyApplication (mapIndices f ty) (map (mapIndices f) xs)
mapIndices f (OpenFamily slot xs level) = OpenFamily slot (map (mapIndices f) xs) level
mapIndices f (FamilyExpression domain slot body level) = FamilyExpression (mapIndices f domain) slot (mapIndices f body) level
mapIndices _ ty = ty

-- Family lambda binders are distinct from runtime telescope positions. Their
-- identities are local implementation details, normalized before caching.
familyLocals :: Type -> S.Set Int
familyLocals = free S.empty
  where
    free bound (FamilyExpression domain slot body _) = free bound domain `S.union` free (S.insert slot bound) body
    free bound (Named _ xs) = S.unions (map (free bound) xs)
    free bound (Callable a b) = S.unions (map (free (S.insert (-1) bound)) (b:a))
    free bound (SchemaValue ds _) = S.unions (map (free bound) ds)
    free bound (SelectedFamily value) = free bound value
    free bound (FamilyApplication f xs) = S.unions (map (free bound) (f:xs))
    free bound (OpenFamily _ xs _) = S.unions (map (free bound) xs)
    free bound (Runtime domain index) = free bound domain `S.union` indices bound index
    free _ _ = S.empty
    indices bound (IndexLocal i) = if S.member i bound then S.empty else S.singleton i
    indices bound IndexArgument{} = if S.member (-1) bound then S.empty else S.singleton (-1)
    indices bound (IndexTyped ty x) = free bound ty `S.union` indices bound x
    indices bound (IndexLambda slots ty x) = free bound ty `S.union` indices (bound `S.union` S.fromList slots) x
    indices bound (IndexApply f x) = indices bound f `S.union` indices bound x
    indices bound (IndexConstructor _ ts xs) = S.unions (map (free bound) ts ++ map (indices bound) xs)
    indices bound (IndexProject _ ts x) = S.unions (indices bound x:map (free bound) ts)
    indices bound (IndexCall _ ts xs) = S.unions (map (free bound) ts ++ map (indices bound) xs)
    indices bound (IndexSuccessor x) = indices bound x
    indices _ _ = S.empty

canonicalFamilies :: Type -> Type
canonicalFamilies = canonicalFamiliesAvoiding S.empty

canonicalFamiliesAvoiding :: S.Set Int -> Type -> Type
canonicalFamiliesAvoiding avoid ty = go M.empty start ty
  where
    start = maybe 0 (+1) (S.lookupMax (avoid `S.union` familyLocals ty))
    go names next (FamilyExpression domain slot body level) = FamilyExpression (go names next domain) next
      (go (M.insert slot next names) (next+1) body) level
    go names next (Named s xs) = Named s (map (go names next) xs)
    go names next (Callable a b) = Callable (map (go names next) a) (go names next b)
    go names next (SchemaValue ds l) = SchemaValue (map (go names next) ds) l
    go names next (SelectedFamily value) = SelectedFamily (go names next value)
    go names next (FamilyApplication f xs) = FamilyApplication (go names next f) (map (go names next) xs)
    go names next (OpenFamily i xs l) = OpenFamily i (map (go names next) xs) l
    go names next (Runtime domain index) = Runtime (go names next domain) (ix names next index)
    go _ _ t = t
    ix names _ (IndexLocal i) = IndexLocal (M.findWithDefault i i names)
    ix names next (IndexConstructor c ts xs) = IndexConstructor c (map (go names next) ts) (map (ix names next) xs)
    ix names next (IndexProject f ts x) = IndexProject f (map (go names next) ts) (ix names next x)
    ix names next (IndexCall f ts xs) = IndexCall f (map (go names next) ts) (map (ix names next) xs)
    ix names next (IndexSuccessor x) = IndexSuccessor (ix names next x)
    ix names next (IndexTyped ty x) = typedIndex (go names next ty) (ix names next x)
    ix names next (IndexLambda slots ty x) =
      let fresh = take (length slots) [next..]
      in IndexLambda fresh (go names next ty) (ix (M.union (M.fromList (zip slots fresh)) names) (next+length slots) x)
    ix names next (IndexApply f x) = IndexApply (ix names next f) (ix names next x)
    ix _ _ x = x

applyTypeFamily :: Type -> [Type] -> Either Refusal Type
applyTypeFamily family@(SelectedFamily (Runtime (SchemaValue [] _) _)) [] = Right (FamilyApplication family [])
applyTypeFamily family [] = Right family
applyTypeFamily family@(FamilyExpression domain _ _ _) (Runtime actual value:rest) | domain == actual =
  case canonicalFamiliesAvoiding (familyLocals (Runtime actual value)) family of
    FamilyExpression _ slot body _ -> applyTypeFamily (canonicalFamilies (replaceLocal slot body)) rest
    _ -> refuse Semantics "Missing type-family binder"
  where
    replaceLocal slot = mapIndices (replace slot)
    replace slot (IndexLocal i) | i == slot = value
    replace slot (IndexConstructor c ts xs) = IndexConstructor c (map (replaceLocal slot) ts) (map (replace slot) xs)
    replace slot (IndexProject f ts x) = IndexProject f (map (replaceLocal slot) ts) (replace slot x)
    replace slot (IndexCall f ts xs) = IndexCall f (map (replaceLocal slot) ts) (map (replace slot) xs)
    replace slot (IndexSuccessor x) = IndexSuccessor (replace slot x)
    replace slot (IndexTyped ty x) = typedIndex (replaceLocal slot ty) (replace slot x)
    replace slot (IndexLambda slots ty x) = IndexLambda slots (replaceLocal slot ty) (replace slot x)
    replace slot (IndexApply f x) = IndexApply (replace slot f) (replace slot x)
    replace _ x = x
applyTypeFamily FamilyExpression{} _ = refuse Semantics "Type-family lambda has incompatible index arguments"
applyTypeFamily family xs = do
  (domains,level) <- familyTelescope family
  unless (length xs <= length domains) (refuse Semantics "Type-family application has too many indices")
  forM_ (zip [0..] xs) $ \(i,arg) -> case arg of
    Runtime actual _ -> unless (actual == bindFamilyInputs (take i xs) (domains !! i))
      (refuse Semantics "Type-family index has an incompatible dependent domain")
    _ -> refuse Semantics "Type-family index is not a checked value"
  let locals = S.unions (map familyLocals (family:xs))
      firstSlot = maybe 0 (+1) (S.lookupMax locals)
      abstract _ prior [] = FamilyApplication family prior
      abstract slot prior (domain:rest) =
        let actual = bindFamilyInputs prior domain
        in FamilyExpression actual slot (abstract (slot+1) (prior ++ [Runtime actual (IndexLocal slot)]) rest) level
  pure (abstract firstSlot xs (drop (length xs) domains))

familyTelescope :: Type -> Either Refusal ([Type],LevelExpr)
familyTelescope (FamilyParameter _ domains level) = Right (domains,level)
familyTelescope (OpenFamily _ domains level) = Right (domains,level)
familyTelescope (SelectedFamily (Runtime (SchemaValue domains level) _)) = Right (domains,level)
familyTelescope (FamilyExpression domain _ _ level) = Right ([domain],level)
familyTelescope _ = refuse Representation "Type-family application requires an unapplied family"

-- Family telescope positions have their own scope: they are neither caller
-- inputs nor callback arguments. Substitution is simultaneous and leaves the
-- caller's supplied indices untouched.
bindFamilyInputs :: [Type] -> Type -> Type
bindFamilyInputs values = walk
  where
    -- These types introduce their own family telescope. Their local positions
    -- must not be rebound by an application in the enclosing telescope.
    walk ty@OpenFamily{} = ty
    walk ty@FamilyParameter{} = ty
    walk ty@SchemaValue{} = ty
    walk (Named s xs) = Named s (map walk xs)
    walk (Callable a b) = Callable (map walk a) (walk b)
    walk (SelectedFamily t) = SelectedFamily (walk t)
    walk (FamilyApplication f xs) = FamilyApplication (walk f) (map walk xs)
    walk (FamilyExpression d slot b l) = FamilyExpression (walk d) slot (walk b) l
    walk (Runtime ty ix) = Runtime (walk ty) (go ix)
    walk ty = ty
    go (IndexFamilyArgument i) | Runtime _ value:_ <- drop i values = value
    go (IndexTyped ty x) = typedIndex (walk ty) (go x)
    go (IndexLambda slots ty x) = IndexLambda slots (walk ty) (go x)
    go (IndexApply f x) = IndexApply (go f) (go x)
    go (IndexProject f ts x) = IndexProject f (map walk ts) (go x)
    go (IndexCall f ts xs) = IndexCall f (map walk ts) (map go xs)
    go (IndexConstructor f ts xs) = IndexConstructor f (map walk ts) (map go xs)
    go (IndexSuccessor x) = IndexSuccessor (go x)
    go x = x

-- Rebase only the current family's bound positions into the generated value
-- telescope, after any external captures. Earlier domains are instantiated in
-- order, so a later index keeps the precise type of each preceding index.
materializeFamilyDomains :: Int -> [Type] -> [Type]
materializeFamilyDomains prefix = go []
  where
    go _ [] = []
    go prior (domain:rest) =
      let actual = bindFamilyInputs prior domain
      in actual : go (prior ++ [Runtime actual (IndexInput (prefix + length prior))]) rest

captureArguments :: [Type] -> ([Type],[(Type,IndexExpr)])
captureArguments args = let (result,slots) = runState (traverse (visit False S.empty . canonicalFamilies) args) [] in (result,slots)
  where
    visit bound locals (Named symbol xs) = Named symbol <$> traverse (visit bound locals) xs
    visit _ locals (Callable a b) = Callable <$> traverse (visit True locals) a <*> visit True locals b
    visit bound locals (SchemaValue ds l) = SchemaValue <$> traverse (visit bound locals) ds <*> pure l
    visit bound locals (SelectedFamily value) = SelectedFamily <$> visit bound locals value
    visit bound locals (FamilyApplication ty xs) = FamilyApplication <$> visit bound locals ty <*> traverse (visit bound locals) xs
    visit bound locals (FamilyExpression domain slot body level) = FamilyExpression <$> visit bound locals domain <*> pure slot
      <*> visit bound (S.insert slot locals) body <*> pure level
    visit bound locals (Runtime ty ix) = do
      domain <- visit bound locals ty
      let erase (IndexLocal slot) | S.member slot locals = IndexCaptured 0
          erase (IndexConstructor c ts xs) = IndexConstructor c ts (map erase xs)
          erase (IndexSuccessor x) = IndexSuccessor (erase x)
          erase (IndexProject f ts x) = IndexProject f ts (erase x)
          erase (IndexCall f ts xs) = IndexCall f ts (map erase xs)
          -- A callback argument is bound inside its callable telescope. When
          -- specializing a carrier used by that telescope, it is instead a
          -- free value and must become an explicit captured index.
          erase IndexArgument{} = if bound then IndexCaptured 0 else IndexInput 0
          erase (IndexTyped ty x) = typedIndex (mapIndices erase ty) (erase x)
          erase (IndexLambda slots ty x) = IndexLambda slots (mapIndices erase ty) (erase x)
          erase (IndexApply f x) = IndexApply (erase f) (erase x)
          erase x = x
          localsInIndex = familyLocals (Runtime domain ix)
          remainingLocals = if bound then localsInIndex else S.delete (-1) localsInIndex
      -- A closed constructor can still have a caller-dependent domain. Decide
      -- whether to capture before that domain's free indices are abstracted;
      -- otherwise an empty indexed value is frozen at an unconstrained index.
      if closed (Runtime ty (erase ix)) || not (S.null remainingLocals)
        then Runtime domain <$> nested bound locals ix else do
        slots <- gets id
        -- A projection's static arguments can contain alpha-equivalent family
        -- lambdas at different nesting depths. Deduplicate by their canonical
        -- binders, otherwise projecting a record changes its capture layout.
        let canonical = canonicalFamilies (Runtime domain (case ix of IndexTyped _ x -> x; _ -> ix))
            value = case canonical of Runtime ty x -> (ty,x); _ -> (domain,ix)
            slot = length (takeWhile (/= value) slots)
        when (slot == length slots) (modify' (++ [value]))
        pure (Runtime domain (IndexCaptured slot))
    visit _ _ ty = pure ty
    nested bound locals (IndexTyped ty ix) = do
      captured <- visit bound locals (Runtime ty ix)
      case captured of
        Runtime _ value -> pure (typedIndex ty value)
        _ -> pure (typedIndex ty ix)
    nested bound locals (IndexLambda slots ty ix) = IndexLambda slots <$> visit bound locals ty
      <*> nested bound (locals `S.union` S.fromList slots) ix
    nested bound locals application@IndexApply{} = case spine [] application of
      (fn@(IndexTyped (Callable domains _) _),values) | length values <= length domains -> do
        capturedFn <- nested bound locals fn
        capturedValues <- forM (zip [0..] values) $ \(i,value) -> do
          captured <- visit bound locals (Runtime (applyCallback (take i values) (domains !! i)) value)
          case captured of Runtime _ ix -> pure ix; _ -> pure value
        pure (foldl IndexApply capturedFn capturedValues)
      _ | IndexApply f x <- application -> IndexApply <$> nested bound locals f <*> nested bound locals x
        | otherwise -> pure application
    nested bound locals (IndexCall f ts xs) = IndexCall f <$> traverse (visit bound locals) ts <*> traverse (nested bound locals) xs
    nested bound locals (IndexConstructor f ts xs) = IndexConstructor f <$> traverse (visit bound locals) ts <*> traverse (nested bound locals) xs
    nested bound locals (IndexProject f ts x) = IndexProject f <$> traverse (visit bound locals) ts <*> nested bound locals x
    nested bound locals (IndexSuccessor x) = IndexSuccessor <$> nested bound locals x
    nested _ _ ix = pure ix
    spine values (IndexApply f x) = spine (x:values) f
    spine values fn = (fn,values)

shiftIndices :: Int -> Type -> Type
shiftIndices offset = mapIndices go
  where
    go (IndexInput i) = IndexInput (i+offset)
    go (IndexSuccessor i) = IndexSuccessor (go i)
    go (IndexConstructor c ts xs) = IndexConstructor c (map (shiftIndices offset) ts) (map go xs)
    go (IndexProject f ts i) = IndexProject f (map (shiftIndices offset) ts) (go i)
    go (IndexCall f ts xs) = IndexCall f (map (shiftIndices offset) ts) (map go xs)
    go (IndexTyped ty x) = typedIndex (mapIndices go ty) (go x)
    go (IndexLambda slots ty x) = IndexLambda slots (mapIndices go ty) (go x)
    go (IndexApply f x) = IndexApply (go f) (go x)
    go ix = ix

materializeCaptures :: Type -> Type
materializeCaptures = mapIndices go
  where
    go (IndexCaptured slot) = IndexInput slot
    go (IndexSuccessor i) = IndexSuccessor (go i)
    go (IndexConstructor c ts xs) = IndexConstructor c (map materializeCaptures ts) (map go xs)
    go (IndexProject f ts x) = IndexProject f (map materializeCaptures ts) (go x)
    go (IndexCall f ts xs) = IndexCall f (map materializeCaptures ts) (map go xs)
    go (IndexTyped ty x) = typedIndex (mapIndices go ty) (go x)
    go (IndexLambda slots ty x) = IndexLambda slots (mapIndices go ty) (go x)
    go (IndexApply f x) = IndexApply (go f) (go x)
    go ix = ix

staticArguments :: [Type] -> [Type]
staticArguments = takeWhile (\x -> case x of Runtime{} -> False; _ -> True)
data ParameterKind = UnusedKind | LevelKind | TypeKind LevelExpr | FamilyKind [Type] LevelExpr deriving (Eq,Show)
data ArgumentSlot = TypePosition Int | ValuePosition Int deriving (Eq,Show)
data Signature = Signature { parameters :: Int, inputs :: [Type], output :: Type, dropped :: Int
  , parameterKinds :: [ParameterKind], argumentSlots :: [ArgumentSlot] }
  deriving (Eq,Show)

-- Stored family values already have a runtime schema representation. Preserve
-- that choice after a value binder, while admitting later type/level binders.
staticKind :: [Type] -> ParameterKind -> Bool
staticKind ins FamilyKind{} = null ins
staticKind _ _ = True

runtimeDropped :: Signature -> Int
runtimeDropped sig = length [() | ValuePosition{} <- take (dropped sig) (argumentSlots sig)]

-- Internal types group static arguments before value indices. Checked source
-- terms and compiled trees retain their original, potentially mixed order.
sourceArguments :: [ArgumentSlot] -> [a] -> [a] -> Either Refusal [a]
sourceArguments slots types values = traverse pick slots
  where
    pick (TypePosition i) = at i types
    pick (ValuePosition i) = at i values
data Instance = Instance { origin :: Text, arguments :: [Type], identity :: Text } deriving (Eq,Show)
data Result = Result { inventory :: Inventory, instances :: [Instance], failures :: M.Map Text Refusal
  , directRoots :: S.Set Text, runtimeClosure :: S.Set Text, openRoots :: M.Map Text Text
  , statementRoots :: M.Map Text (Either Refusal Text)
  , statementDependencies :: M.Map Text (S.Set (Text,Text)) }
data Store = Store { ready :: M.Map Text Value, recorded :: M.Map Text Instance }
type Build = ExceptT Refusal (State Store)

abort :: Category -> Text -> Build a
abort kind = throwError . refusal kind

set :: Text -> Value -> Value -> Value
set k x (Object o) = Object (KM.insert (K.fromText k) x o)
set _ _ x = x
number :: Value -> Either Refusal Int
number (Number n) = maybe (refuse Syntax "Invalid compiler index") Right (toBoundedInteger n)
number _ = refuse Syntax "Missing compiler index"
at :: Int -> [a] -> Either Refusal a
at i xs | i >= 0 = case drop i xs of x:_ -> Right x; _ -> refuse Syntax "Index outside checked environment"
at _ _ = refuse Syntax "Negative compiler index"
app :: Value -> Either Refusal Value
app e | get "tag" e == String "apply" = Right (get "value" (get "argument" e))
      | otherwise = refuse Syntax "Type or value argument is not an application"

-- Closed levels use arbitrary-precision naturals; symbolic levels are maxima
-- of a constant and parameter offsets. Argument kind is retained separately.
natural :: Value -> Either Refusal Integer
natural (Number n) = case floatingOrInteger n :: Either Double Integer of
  Right x | x >= 0 -> Right x
  _ -> refuse Syntax "Invalid universe-level natural"
natural _ = refuse Syntax "Missing universe-level natural"
levelConstant :: Integer -> LevelExpr
levelConstant n = LevelExpr n M.empty
levelParameter :: Int -> LevelExpr
levelParameter i = LevelExpr 0 (M.singleton (BoundLevel i) 0)
openLevel :: Int -> LevelExpr
openLevel i = LevelExpr 0 (M.singleton (RigidLevel i) 0)
normalLevel :: LevelExpr -> LevelExpr
normalLevel (LevelExpr n xs) = LevelExpr (if any (>= n) (M.elems xs) then 0 else n) xs
joinLevel :: LevelExpr -> LevelExpr -> LevelExpr
joinLevel (LevelExpr n xs) (LevelExpr m ys) = normalLevel (LevelExpr (max n m) (M.unionWith max xs ys))
shiftLevel :: Integer -> LevelExpr -> LevelExpr
shiftLevel n (LevelExpr m xs) = normalLevel (LevelExpr (n+m) (M.map (+n) xs))
levelNumber :: LevelExpr -> Either Refusal Integer
levelNumber (LevelExpr n xs) | M.null xs = Right n
levelNumber _ = refuse Representation "Unresolved universe level"
levelValue :: LevelExpr -> Value
levelValue l@(LevelExpr n xs) = case levelNumber l of
  Right value -> toJSON value
  Left _ -> object ["constant" .= n,"parameters" .= [(i,k) | (BoundLevel i,k) <- M.toAscList xs]
    ,"openParameters" .= [(i,k) | (RigidLevel i,k) <- M.toAscList xs]]
readLevelValue :: Value -> Either Refusal LevelExpr
readLevelValue value@(Number _) = levelConstant <$> natural value
readLevelValue value = do
  n <- natural (get "constant" value)
  bound <- entries BoundLevel (get "parameters" value)
  rigid <- entries RigidLevel (get "openParameters" value)
  pure (normalLevel (LevelExpr n (M.fromListWith max (bound ++ rigid))))
  where
    entries atom (Array xs) = forM (foldr (:) [] xs) $ \x -> case array x of
      [slot,offset] -> (,) <$> (atom <$> number slot) <*> natural offset
      _ -> refuse Syntax "Invalid symbolic universe-level term"
    entries _ _ = refuse Syntax "Missing symbolic universe-level terms"
builtin :: Inventory -> Text -> Text
builtin inv key = string (get key (get "builtins" (document inv)))
levelSymbols :: Inventory -> S.Set Text
levelSymbols inv = S.fromList (filter (not . T.null) [builtin inv k | k <- ["level","levelUniverse","levelZero","levelSuc","levelMax"]])
isLevelType :: Inventory -> Value -> Bool
isLevelType inv ty = let t = get "term" ty; s = builtin inv "level" in
  not (T.null s) && get "tag" t == String "definition" && get "symbol" t == String s
  && null (array (get "eliminations" t))
isUniverse :: Value -> Bool
isUniverse ty = let t = get "term" ty; s = get "sort" t in
  get "tag" t == String "sort" && get "tag" s == String "universe" && get "kind" s == String "UType"

readLevel :: Inventory -> [Maybe Type] -> Value -> Either Refusal LevelExpr
readLevel inv env value = do
  n <- natural (get "constant" value)
  terms <- forM (array (get "maximum" value)) $ \entry -> do
    offset <- natural (get "offset" entry)
    shiftLevel offset <$> readLevelTerm inv env (get "term" entry)
  pure (foldl joinLevel (levelConstant n) terms)

readLevelTerm :: Inventory -> [Maybe Type] -> Value -> Either Refusal LevelExpr
readLevelTerm inv env t = case string (get "tag" t) of
  "native-open-level" -> openLevel <$> number (get "slot" t)
  "level" -> readLevel inv env (get "level" t)
  "variable" -> do
    unless (null (array (get "eliminations" t))) (refuse Representation "Applied universe-level variable")
    i <- number (get "index" t)
    at i env >>= \x -> case x of
      Just (Level l) -> Right l
      _ -> refuse Semantics "Runtime or type variable used as a universe level"
  "definition" -> do
    let s = string (get "symbol" t)
    es <- traverse app (array (get "eliminations" t))
    case es of
      [] | s == builtin inv "levelZero" && not (T.null s) -> Right (levelConstant 0)
      [x] | s == builtin inv "levelSuc" && not (T.null s) -> shiftLevel 1 <$> readLevelTerm inv env x
      [x,y] | s == builtin inv "levelMax" && not (T.null s) -> joinLevel <$> readLevelTerm inv env x <*> readLevelTerm inv env y
      _ -> refuse Syntax "Unknown or malformed universe-level operation"
  _ -> refuse Representation "Unresolved or unsupported universe-level term"

-- NoAbs codomains retain the previous context; Abs codomains extend it.
readType :: Inventory -> [Maybe Type] -> Value -> Either Refusal Type
readType inv env = readTypeWithExpected inv env Nothing

-- A checked reduction may expose a constructor with omitted parameters. Keep
-- the caller's expected carrier so those parameters come from the complete
-- dependent result, rather than guessing a family from a single member.
readTypeWithExpected :: Inventory -> [Maybe Type] -> Maybe Type -> Value -> Either Refusal Type
readTypeWithExpected inv env expected t = case string (get "tag" t) of
  "native-schema-value" -> SchemaValue <$> traverse (readType inv env) (array (get "domains" t)) <*> readLevelValue (get "universe" t)
  "sort" | isUniverse (object ["term" .= t]) -> SchemaValue [] <$> readLevel inv env (get "level" (get "sort" t))
  "pi" -> do
    kind <- parameterKind inv env (object ["term" .= t])
    case kind of
      Just (FamilyKind domains level) -> pure (SchemaValue domains level)
      _ -> callback env [] t
  "native-open-type" -> Open <$> number (get "slot" t) <*> readLevelValue (get "universe" t)
  "native-open-family" -> do
    domains <- traverse (readType inv env) (array (get "domains" t))
    family <- OpenFamily <$> number (get "slot" t) <*> pure domains <*> readLevelValue (get "universe" t)
    applyFamily family domains (array (get "eliminations" t))
  "level" -> Level <$> readLevelTerm inv env t
  "variable" -> do
    i <- number (get "index" t)
    value <- at i env >>= maybe (refuse Syntax "Missing runtime index binding") Right
    let es = array (get "eliminations" t)
    case value of
      FamilyParameter _ domains _ -> applyFamily value domains es
      OpenFamily _ domains _ -> applyFamily value domains es
      FamilyExpression domain _ _ _ -> applyFamily value [domain] es
      SelectedFamily (Runtime (SchemaValue domains _) _) -> applyFamily value domains es
      _ -> eliminateIndices inv env value es
  "constructor" -> do
    let c = string (get "symbol" t)
    if c `elem` [builtin inv "zero",builtin inv "suc"] && not (T.null c)
      then readIndex inv env (Named (builtin inv "nat") []) t
      else do
        readConstructorIndex inv env expected t
  "literal" | get "tag" (get "literal" t) == String "natural" ->
    Runtime (Named (builtin inv "nat") []) . IndexNatural <$> natural (get "value" (get "literal" t))
  "definition" | string (get "symbol" t) `S.member` S.fromList (filter (not . T.null) [builtin inv k | k <- ["levelZero","levelSuc","levelMax"]]) ->
    Level <$> readLevelTerm inv env t
  "definition" -> do
    let name = string (get "symbol" t)
        es = array (get "eliminations" t)
    case M.lookup name (declarations inv) of
      Just d | get "moduleInstanceCopy" d == Bool True
        ,get "kind" d `elem` map String ["datatype","record"] ->
          case Reduction.reduceHead inv t of
            Just (reduced,_) -> readType inv env reduced
            Nothing -> refuse Representation "Module carrier alias lacks a checked reducible equation"
      Just d | get "kind" d `elem` [String "function",String "primitive"] -> do
        declared <- field inv "type" d
        projection <- field inv "projection" d
        if get "proper" projection /= Null then readFunctionType d name es
        else if returnsUniverse declared then do
          unless (get "abstract" d == Bool False && get "opaque" d == Bool False && terminationChecked inv d)
            (refuse Semantics "Type alias is not transparently terminating")
          case Reduction.reduceHead inv t of
            Just (reduced,_) -> readType inv env reduced
            Nothing -> refuse Representation "Type alias requires known checked arguments"
        else readFunctionType d name es
      Just d | get "kind" d `elem` [String "record",String "datatype"] -> do
        (kinds,indices,_,slots) <- familyLayout inv d
        let count = length kinds
        unless (length es == count + length indices) (refuse Syntax "Family application arity mismatch")
        let staticEs = [e | (TypePosition _,e) <- zip slots es]
            valueEs = [e | (ValuePosition _,e) <- zip slots es]
        args <- readStaticArguments inv env kinds staticEs
        -- Later index domains may depend on earlier index values. Their
        -- telescope positions are not runtime inputs of the enclosing term.
        -- Instantiate both namespaces together: supplied arguments can
        -- themselves mention types and values in the caller's telescope.
        values <- foldM (\prior (domain,e) -> do
          contextual <- instantiate args (M.fromList (zip [0..] [ix | Runtime _ ix <- prior])) domain
          value <- app e >>= readIndex inv env contextual
          pure (prior ++ [value])) [] (zip indices valueEs)
        pure (Named name (args ++ values))
      _ -> Named name <$> traverse (app >=> readType inv env) es
  _ -> refuse Representation "Type expression is outside named first-order families"
  where
    callback context domains arrow | get "tag" arrow == String "pi" = do
      let dom = get "domain" arrow; cod = get "codomain" arrow
          modality = get "info" dom
      unless (get "relevance" modality == String "relevant" && get "quantity" modality /= String "zero")
        (refuse Semantics "Erased callback argument requires a separate representation rule")
      domain <- readType inv context (get "term" (get "type" dom))
      unless (valueCarrier domain) (refuse Representation "Callback requires first-order arguments and result")
      let context' = if get "binds" cod == Bool False then context
            else Just (Runtime domain (IndexArgument (length domains))):context
      callback context' (domains ++ [domain]) (get "term" (get "body" cod))
    callback context domains result = do
      out <- readType inv context result
      unless (valueCarrier out) (refuse Representation "Callback requires first-order arguments and result")
      pure (Callable domains out)
    valueCarrier Runtime{} = False
    valueCarrier Level{} = False
    valueCarrier SchemaValue{} = False
    valueCarrier Unused = False
    valueCarrier t = firstOrder t
    -- Proven-unused module arguments are static bookkeeping inside a carrier,
    -- not function-valued data. They cannot themselves be callback domains.
    firstOrder Unused = True
    firstOrder Callable{} = False
    firstOrder (SchemaValue ds _) = all firstOrder ds
    firstOrder (SelectedFamily value) = firstOrder value
    firstOrder (Runtime ty _) = firstOrder ty
    firstOrder (Named _ xs) = all firstOrder xs
    firstOrder Parameter{} = True
    firstOrder Open{} = True
    firstOrder Level{} = True
    firstOrder (FamilyApplication f xs) = firstOrder f && all firstOrder xs
    firstOrder FamilyParameter{} = True
    firstOrder OpenFamily{} = True
    firstOrder (FamilyExpression a _ b _) = firstOrder a && firstOrder b
    firstOrder _ = False
    applyFamily family _ es = foldM (\current e -> do
      (domains,_) <- familyTelescope current
      domain <- at 0 domains
      arg <- app e >>= readIndex inv env domain
      applyTypeFamily current [arg]) family es
    readFunctionType d name es = do
        projection <- field inv "projection" d
        if get "proper" projection /= Null then case es of
          _ -> do
            position <- subtract 1 <$> number (get "index" projection)
            e <- at position es
            let rest = drop (position+1) es
            receiver <- app e >>= readType inv env
            projected <- projectIndex inv receiver (object ["tag" .= ("project" :: Text),"symbol" .= name])
            eliminateIndices inv env projected rest
        else do
          sig <- signature inv d
          if dropped sig > 0 then readOmittedIndexCall inv env sig name es
            else readCompleteIndexCall sig name es
    readCompleteIndexCall sig name es = do
          let count = parameters sig
          let arity = count + length (inputs sig)
          unless (runtimeDropped sig == 0 && length es >= arity)
            (refuse Representation "Computed index helper must supply its complete runtime argument list")
          let staticEs = [e | (TypePosition _,e) <- zip (argumentSlots sig) es]
              valueEs = [e | (ValuePosition _,e) <- zip (argumentSlots sig) es]
          args <- readStaticArguments inv env (parameterKinds sig) staticEs
          let values prior [] = do
                out <- instantiate args (M.fromList (zip [0..] prior)) (output sig)
                eliminateIndices inv env (Runtime out (IndexCall name args prior)) (drop arity es)
              values prior ((e,domain):rest) = do
                contextual <- instantiate args (M.fromList (zip [0..] prior)) domain
                term <- app e
                case readIndex inv env contextual term of
                  Right (Runtime actual ix) -> values
                    (prior ++ [case actual of Callable{} -> typedIndex actual ix; _ -> ix]) rest
                  Right _ -> refuse Semantics "Computed index argument is not a value"
                  Left failure -> case contextual of
                    -- A static family and a stored schema are not interchangeable
                    -- runtime values. A checked transparent equation can instead
                    -- eliminate the call at these actual source arguments. Retain
                    -- the caller's scope and require the same family telescope;
                    -- blocked reduction preserves the original refusal.
                    SchemaValue domains level
                      | Right family <- readType inv env term
                      , Right (actualDomains,actualLevel) <- familyTelescope family
                      , indexNormalForm (SchemaValue actualDomains actualLevel)
                          == indexNormalForm (SchemaValue domains level)
                      , Just (reduced,_) <- Reduction.reduceHead inv t -> readTypeWithExpected inv env expected reduced
                    _ -> Left failure
          values [] (zip valueEs (inputs sig))

-- Projection-like checked calls omit a source prefix. Infer that prefix only
-- from the supplied values' declared types, then recheck the whole application.
-- Signature-local inputs and caller indices remain separate during inference.
readOmittedIndexCall :: Inventory -> [Maybe Type] -> Signature -> Text -> [Value] -> Either Refusal Type
readOmittedIndexCall inv env sig name es = do
  let slots = drop (dropped sig) (argumentSlots sig)
  unless (length es >= length slots) (refuse Representation "Computed index call lacks a supplied argument")
  explicit <- fmap M.fromList $ forM [(i,e) | (TypePosition i,e) <- zip slots es] $ \(i,e) -> do
    value <- if parameterKinds sig !! i == UnusedKind then app e >> pure Unused else app e >>= readType inv env
    pure (i,value)
  (known,indices,actuals) <- foldM step (explicit,M.empty,[]) [(i,e) | (ValuePosition i,e) <- zip slots es]
  completed <- foldM complete known (zip [0..] (parameterKinds sig))
  args <- traverse (\i -> maybe (refuse Representation "Cannot recover computed index type parameter") Right
    (M.lookup i completed)) [0..parameters sig-1]
  values <- traverse (\i -> maybe (refuse Representation "Cannot recover computed index value parameter") Right
    (M.lookup i indices)) [0..length (inputs sig)-1]
  forM_ actuals $ \(i,actual) -> do
    expected <- instantiate args (M.fromList (zip [0..] values)) (inputs sig !! i)
    unless (expected == actual) (refuse Semantics "Recovered computed index argument domain mismatch")
  out <- instantiate args (M.fromList (zip [0..] values)) (output sig)
  eliminateIndices inv env (Runtime out (IndexCall name args values)) (drop (length slots) es)
  where
    step (known,indices,actuals) (i,e) = do
      actual <- app e >>= readType inv env
      case actual of
        Runtime domain ix -> do
          next <- unify known (inputs sig !! i) domain
          recovered <- recover indices (inputs sig !! i) domain
          let value = case domain of Callable{} -> typedIndex domain ix; _ -> ix
          bound <- bind recovered i value
          pure (next,bound,actuals ++ [(i,domain)])
        _ -> refuse Semantics "Computed index argument is not a runtime value"
    bind known i value = case M.lookup i known of
      Nothing -> Right (M.insert i value known)
      Just prior | prior == value -> Right known
      _ -> refuse Semantics "Inconsistent recovered computed index"
    recover known (Runtime _ (IndexInput i)) (Runtime _ value)
      | i < runtimeDropped sig = bind known i value
    recover known (Named s xs) (Named t ys) | s == t && length xs == length ys =
      foldM (\table (x,y) -> recover table x y) known (zip xs ys)
    recover known (FamilyApplication _ xs) (FamilyApplication _ ys) | length xs == length ys =
      foldM (\table (x,y) -> recover table x y) known (zip xs ys)
    recover known _ _ = Right known
    complete table (i,UnusedKind) = Right (M.insert i Unused table)
    complete table (i,TypeKind level) = case M.lookup i table of
      Just ty | closed ty -> universeOf inv ty >>= constrainUniverse table level
      _ -> Right table
    complete table _ = Right table

returnsUniverse :: Value -> Bool
returnsUniverse ty | get "tag" (get "term" ty) == String "pi" = returnsUniverse (get "body" (get "codomain" (get "term" ty)))
                   | otherwise = isUniverse ty

readStaticArguments :: Inventory -> [Maybe Type] -> [ParameterKind] -> [Value] -> Either Refusal [Type]
readStaticArguments inv env kinds elims = foldM step [] (zip kinds elims)
  where
    step prior (UnusedKind,e) = app e >> pure (prior ++ [Unused])
    step prior (FamilyKind domains level,e) = do
      term <- app e
      inputs <- traverse (substitute prior) domains
      expectedLevel <- substituteLevel prior level
      let locals = S.unions [familyLocals t | Just t <- env]
          firstSlot = maybe 0 (+1) (S.lookupMax locals)
          abstract context _ _ [] value = readType inv context value
          abstract context slot supplied (domain:rest) value = do
            let actual = bindFamilyInputs supplied domain
                bound = Runtime actual (IndexLocal slot)
            (next,body) <- if get "tag" value == String "lambda" then do
              let abstraction = get "abstraction" value
              pure (if get "binds" abstraction == Bool True then Just bound:context else context,
                get "body" abstraction)
              else do
                applied <- maybe (refuse Representation "Cannot eta-expand a type-family argument") Right
                  (Reduction.applyTerms (Reduction.shift 1 value) [Reduction.variable 0])
                pure (Just bound:context,applied)
            FamilyExpression actual slot <$> abstract next (slot+1) (supplied ++ [bound]) rest body
              <*> pure expectedLevel
      value <- if get "tag" term == String "lambda" then abstract env firstSlot [] inputs term
        else case readType inv env term of
          Right value -> pure value
          Left _ -> abstract env firstSlot [] inputs term
      pure (prior ++ [value])
    step prior (_,e) = (prior ++) . (:[]) <$> (app e >>= readType inv env)

-- Only checked, transparent, terminating, nullary type definitions reduce here.
-- The original declaration remains in the inventory and obligation report.
typeAlias :: Inventory -> Value -> Either Refusal (Maybe Type)
typeAlias inv d | get "kind" d == String "function" = do
  ty <- field inv "type" d
  if not (isUniverse ty) then pure Nothing else do
    unless (get "abstract" d == Bool False && get "opaque" d == Bool False
      && terminationChecked inv d) (refuse Semantics "Type alias is not transparently terminating")
    tree <- field inv "compiled" d
    unless (get "tag" tree == String "done" && null (array (get "binders" tree)))
      (refuse Representation "Type alias requires static computation")
    Just <$> readType inv [] (get "body" tree)
typeAlias _ _ = pure Nothing

-- A finite constructor can have phantom static parameters. Its expected index
-- domain determines those parameters; source constructor terms omit them.
readIndex :: Inventory -> [Maybe Type] -> Type -> Value -> Either Refusal Type
readIndex inv env expected term
  | callable@Callable{} <- expected,get "tag" term == String "lambda" = readIndexClosure inv env callable term
  | get "tag" term == String "native-family-input" =
      Runtime expected . IndexFamilyArgument <$> number (get "index" term)
  | expected == Named (builtin inv "nat") [] && not (T.null (builtin inv "nat"))
  ,get "tag" term == String "constructor" = do
      es <- traverse app (array (get "eliminations" term))
      let symbol = string (get "symbol" term)
      index <- case es of
        [] | symbol == builtin inv "zero" -> Right (IndexNatural 0)
        [arg] | symbol == builtin inv "suc" -> do
          value <- readIndex inv env expected arg
          case value of Runtime _ ix -> Right (IndexSuccessor ix); _ -> refuse Syntax "Missing natural predecessor index"
        _ -> refuse Representation "Unsupported natural index constructor"
      pure (Runtime expected index)
  | get "tag" term == String "constructor" = do
      actual <- readConstructorIndex inv env (Just expected) term
      case actual of
        Runtime domain _ | checkedIndexNormalForm inv domain == checkedIndexNormalForm inv expected -> Right actual
        _ -> refuse Semantics "Index constructor has the wrong declared domain"
  | otherwise = do
      actual <- case readTypeWithExpected inv env (Just expected) term of
        Left failure | callable@Callable{} <- expected ->
          either (const (Left failure)) Right (readIndexClosure inv env callable term)
        result -> result
      let value = case actual of
            SelectedFamily bound -> bound
            FamilyApplication (SelectedFamily bound) [] -> bound
            _ -> actual
      case value of
        Runtime domain _ | checkedIndexNormalForm inv domain == checkedIndexNormalForm inv expected -> Right value
        _ -> refuse Semantics ("Index expression has the wrong declared domain: expected "
          <> T.pack (show expected) <> "; actual " <> T.pack (show actual))

-- Comparison only: an applied checked lambda and its beta-reduced body denote
-- the same index. Keep all carrier arguments and runtime indices; no opaque
-- function is inverted or equated merely because its result type matches.
indexNormalForm :: Type -> Type
indexNormalForm = indexNormalFormWith IndexProject

checkedIndexNormalForm :: Inventory -> Type -> Type
checkedIndexNormalForm inv = indexNormalFormWith (constructorProjection inv)

indexNormalFormWith :: (Text -> [Type] -> IndexExpr -> IndexExpr) -> Type -> Type
indexNormalFormWith project = normal . canonicalFamilies
  where
    normal (Named s xs) = Named s (map normal xs)
    normal (Callable xs out) = Callable (map normal xs) (normal out)
    normal (SchemaValue xs level) = SchemaValue (map normal xs) level
    normal (SelectedFamily value) = SelectedFamily (normal value)
    normal (FamilyApplication family xs) = FamilyApplication (normal family) (map normal xs)
    normal (OpenFamily slot xs level) = OpenFamily slot (map normal xs) level
    normal (FamilyExpression domain slot body level) = FamilyExpression (normal domain) slot (normal body) level
    normal (Runtime domain value) =
      let actual = normal domain
          checked = index value
      -- Only a redundant annotation at an already checked value boundary is
      -- transparent. Applied callback heads still need their type evidence;
      -- a different annotation must not justify equality of the two domains.
      in Runtime actual (case checked of
        IndexTyped annotation expression | annotation == actual -> expression
        _ -> checked)
    normal ty = ty
    index (IndexTyped ty x) = typedIndex (normal ty) (index x)
    index (IndexLambda slots ty x) = IndexLambda slots (normal ty) (index x)
    index (IndexApply f x) = beta (IndexApply (index f) (index x))
    index (IndexProject f ts x) = project f (map normal ts) (index x)
    index (IndexCall f ts xs) = IndexCall f (map normal ts) (map index xs)
    index (IndexConstructor f ts xs) = IndexConstructor f (map normal ts) (map index xs)
    index (IndexSuccessor x) = IndexSuccessor (index x)
    index x = x
    spine (IndexApply f x) xs = spine f (x:xs)
    spine (IndexTyped _ f) xs = spine f xs
    spine f xs = (f,xs)
    beta expression = case spine expression [] of
      (IndexLambda slots _ body,args) | length args >= length slots ->
        index (foldl IndexApply (bindIndexLocals (zip slots args) body) (drop (length slots) args))
      _ -> expression

-- Comparison only, on an already typed index. Checked record metadata fixes
-- the constructor and field order; contextual value parameters precede fields
-- in an IndexConstructor. Unknown or incompatible metadata leaves the original
-- expression intact. This never unfolds a helper or equates arbitrary evidence.
constructorProjection :: Inventory -> Text -> [Type] -> IndexExpr -> IndexExpr
constructorProjection inv name args receiver@(IndexConstructor constructorName constructorArgs values) =
  either (const original) id $ do
    constructor <- lookupDefinition constructorName
    owner <- field inv "family" constructor
    record <- lookupDefinition (string owner)
    projection <- lookupDefinition name
    metadata <- field inv "projection" projection
    count <- field inv "parameters" record >>= number
    constructorCount <- field inv "parameters" constructor >>= number
    declared <- field inv "constructor" record
    fields <- map string . array <$> field inv "fields" record
    let prefix = count - length constructorArgs
    unless (get "kind" constructor == String "constructor" && get "kind" record == String "record"
      && get "kind" projection == String "function"
      && all ((== Bool False) . get "abstract") [constructor,record,projection]
      && get "opaque" projection /= Bool True
      && declared == String constructorName && get "proper" metadata == owner
      && count >= 0 && constructorCount == count && get "index" metadata == toJSON (count+1)
      && map indexNormalForm args == map indexNormalForm constructorArgs
      && prefix >= 0 && length values == prefix + length fields
      && S.size (S.fromList fields) == length fields)
      (refuse Semantics "Record index projection lacks matching checked metadata")
    position <- case [i | (i,f) <- zip [0..] fields,f == name] of
      [i] -> Right i
      _ -> refuse Syntax "Record index projection is not a unique declared field"
    at (prefix+position) values
  where
    original = IndexProject name args receiver
    lookupDefinition symbol = maybe (refuse Syntax "Unknown record index declaration") Right
      (M.lookup symbol (declarations inv))
constructorProjection _ name args receiver = IndexProject name args receiver

-- Check a value closure against its complete callback contract. Eta expansion
-- only supplies the missing value binders; the checked helper signature still
-- validates all static arguments, captured values and the result carrier.
readIndexClosure :: Inventory -> [Maybe Type] -> Type -> Value -> Either Refusal Type
readIndexClosure inv env ty@(Callable domains out) term = do
  unless (not (null domains)) (refuse Representation "Empty index closure telescope")
  let firstSlot = maybe 0 (+1) (S.lookupMax (S.unions (familyLocals ty:[familyLocals t | Just t <- env])))
      slots = take (length domains) [firstSlot..]
      positions = map IndexLocal slots
      localDomains = map (applyCallback positions) domains
  (context,body) <- foldM (\(context,value) (slot,domain) -> do
    let bound = Just (Runtime domain (IndexLocal slot))
    if get "tag" value == String "lambda" then do
      let abstraction = get "abstraction" value
      case get "binds" abstraction of
        Bool True -> pure (bound:context,get "body" abstraction)
        Bool False -> pure (context,get "body" abstraction)
        _ -> refuse Syntax "Index closure lacks checked binder information"
    else do
      applied <- maybe (refuse Representation "Cannot eta-expand an index callback") Right
        (Reduction.applyTerms (Reduction.shift 1 value) [Reduction.variable 0])
      pure (bound:context,applied)) (env,term) (zip slots localDomains)
  value <- readIndex inv context (applyCallback positions out) body
  case value of
    Runtime _ ix -> pure (Runtime ty (IndexLambda slots ty ix))
    _ -> refuse Semantics "Index closure result is not a value"
readIndexClosure _ _ _ _ = refuse Representation "Index closure needs a callback contract"

-- Constructor terms omit static parameters. Recover them from the expected
-- result and ordered payload types, then check every dependent payload against
-- the instantiated telescope. No constructor names or schema shapes are assumed.
readConstructorIndex :: Inventory -> [Maybe Type] -> Maybe Type -> Value -> Either Refusal Type
readConstructorIndex inv env expected term = do
  let c = string (get "symbol" term)
  d <- maybe (refuse Syntax "Unknown index constructor") Right (M.lookup c (declarations inv))
  sig <- signature inv d
  let ownerName = case get "family" d of
        String name -> name
        _ -> case output sig of Named name _ -> name; _ -> ""
  owner <- maybe (refuse Syntax "Unknown index constructor family") Right (M.lookup ownerName (declarations inv))
  sourceParameters <- field inv "parameters" owner >>= number
  let runtimeParameters = sourceParameters - parameters sig
      contextual = case expected of
        Just (Named _ xs) -> take runtimeParameters [ix | Runtime _ ix <- xs]
        _ -> []
  unless (runtimeParameters >= 0 && length contextual == runtimeParameters)
    (refuse Representation "Index constructor needs its contextual value parameters")
  values <- traverse app (array (get "eliminations" term))
  unless (length values == length (inputs sig) - runtimeParameters) (refuse Representation "Index constructor payload arity mismatch")
  initial <- maybe (Right M.empty) (unify M.empty (output sig)) expected
  (known,payloads) <- foldM (step sig) (initial,contextual) (zip (drop runtimeParameters (inputs sig)) values)
  final <- complete sig known
  args <- traverse (\i -> maybe (refuse Representation ("Cannot recover index constructor parameter "
    <> T.pack (show i) <> " of " <> c)) Right (M.lookup i final)) [0..parameters sig-1]
  result <- instantiate args (M.fromList (zip [0..] payloads)) (output sig)
  pure (Runtime result (IndexConstructor c args
    (if get "kind" owner == String "record" then payloads else drop runtimeParameters payloads)))
  where
    step sig (known,prior) (domain,value) = do
      completed <- complete sig known
      let args = [M.findWithDefault (Parameter i) i completed | i <- [0..parameters sig-1]]
      -- Telescope indices belong to this constructor; inferred static
      -- arguments and supplied index expressions belong to the caller.
      -- Instantiate both namespaces without rewriting inserted arguments.
      concrete <- instantiate args (M.fromList (zip [0..] prior)) domain
      let contextualConstructor = get "tag" value == String "constructor" && case concrete of Named{} -> True; _ -> False
          determined = all (`M.member` completed) [0..parameters sig-1]
      actual <- if not determined && hasParameter concrete && not contextualConstructor
        then readType inv env value else readIndex inv env concrete value
      case actual of
        Runtime actualDomain ix -> do
          -- A checked payload needs no further inference once every static
          -- argument is known. Its contextual carrier contains caller symbols;
          -- interpreting them again as constructor metavariables captures scope.
          next <- if determined then pure completed else unify completed domain actualDomain
          pure (next,prior ++ [ix])
        _ -> refuse Semantics "Constructor index payload is not a runtime value"
    hasParameter Parameter{} = True
    hasParameter FamilyParameter{} = True
    hasParameter (SchemaValue ds _) = any hasParameter ds
    hasParameter (SelectedFamily value) = hasParameter value
    hasParameter (Named _ xs) = any hasParameter xs
    hasParameter (FamilyApplication f xs) = hasParameter f || any hasParameter xs
    hasParameter (Runtime ty _) = hasParameter ty
    hasParameter _ = False
    -- Signature reading also runs before specialization, when carrier
    -- parameters are symbolic. Only concrete carriers determine a level here.
    complete sig known = foldM step known (zip [0..] (parameterKinds sig))
      where
        step table (i,UnusedKind) = Right (M.insert i Unused table)
        step table (i,TypeKind level) = case M.lookup i table of
          Just ty | closed ty -> universeOf inv ty >>= constrainUniverse table level
          _ -> Right table
        step table _ = Right table

replaceKnownInputs :: M.Map Int IndexExpr -> Type -> Type
replaceKnownInputs values = mapIndices go
  where
    go original@(IndexInput i) = M.findWithDefault original i values
    go (IndexConstructor c ts xs) = IndexConstructor c (map (replaceKnownInputs values) ts) (map go xs)
    go (IndexSuccessor x) = IndexSuccessor (go x)
    go (IndexProject f ts x) = IndexProject f (map (replaceKnownInputs values) ts) (go x)
    go (IndexCall f ts xs) = IndexCall f (map (replaceKnownInputs values) ts) (map go xs)
    go (IndexTyped ty x) = typedIndex (mapIndices go ty) (go x)
    go (IndexLambda slots ty x) = IndexLambda slots (mapIndices go ty) (go x)
    go (IndexApply f x) = IndexApply (go f) (go x)
    go x = x

-- Callback arguments occupy their own lexical scope, independent of the
-- enclosing runtime telescope. Nested runtime function types remain refused.
applyCallback :: [IndexExpr] -> Type -> Type
applyCallback values = walk
  where
    -- A callable embedded in a carrier introduces its own argument scope.
    -- Applying the enclosing callback must not bind that callable's arguments.
    walk ty@Callable{} = ty
    walk (Named s xs) = Named s (map walk xs)
    walk (SchemaValue ds l) = SchemaValue (map walk ds) l
    walk (SelectedFamily value) = SelectedFamily (walk value)
    walk (FamilyApplication f xs) = FamilyApplication (walk f) (map walk xs)
    walk (OpenFamily i ds l) = OpenFamily i (map walk ds) l
    walk (FamilyExpression d slot b l) = FamilyExpression (walk d) slot (walk b) l
    walk (Runtime ty ix) = Runtime (walk ty) (go ix)
    walk ty = ty
    go (IndexArgument i) | i >= 0 && i < length values = values !! i
    go (IndexTyped ty x) = typedIndex (walk ty) (go x)
    go (IndexLambda slots ty x) = IndexLambda slots (walk ty) (go x)
    go (IndexApply f x) = IndexApply (go f) (go x)
    go (IndexConstructor c ts xs) = IndexConstructor c (map (applyCallback values) ts) (map go xs)
    go (IndexProject f ts x) = IndexProject f (map (applyCallback values) ts) (go x)
    go (IndexCall f ts xs) = IndexCall f (map (applyCallback values) ts) (map go xs)
    go (IndexSuccessor x) = IndexSuccessor (go x)
    go x = x

eliminateIndices :: Inventory -> [Maybe Type] -> Type -> [Value] -> Either Refusal Type
eliminateIndices inv env bound@(Runtime (SchemaValue domains _) _) es
  | null es && not (null domains) = Right (SelectedFamily bound)
  | null es = Right (FamilyApplication (SelectedFamily bound) [])
  | otherwise = foldM (\current e -> do
      (remaining,_) <- familyTelescope current
      domain <- at 0 remaining
      value <- app e >>= readIndex inv env domain
      applyTypeFamily current [value]) (SelectedFamily bound) es
eliminateIndices _ _ value [] = Right value
eliminateIndices inv env (Runtime fnType@(Callable domains out) fn) es = do
  unless (length es >= length domains) (refuse Representation "Partial callback application requires runtime closure construction")
  values <- foldM (\prior (domain,e) -> do
    term <- app e
    value <- readIndex inv env (applyCallback prior domain) term
    case value of
      Runtime _ ix -> pure (prior ++ [ix])
      _ -> refuse Semantics "Callback index argument is not a value") [] (zip domains es)
  eliminateIndices inv env (Runtime (applyCallback values out) (foldl IndexApply (typedIndex fnType fn) values)) (drop (length domains) es)
eliminateIndices inv env value (e:es) = projectIndex inv value e >>= \next -> eliminateIndices inv env next es

projectIndex :: Inventory -> Type -> Value -> Either Refusal Type
projectIndex inv (Runtime (Named owner args) receiver) elimination = do
  unless (get "tag" elimination == String "project") (refuse Representation "Applied runtime index variable")
  let name = string (get "symbol" elimination); concrete = staticArguments args
  d <- maybe (refuse Syntax "Unknown index projection") Right (M.lookup name (declarations inv))
  p <- field inv "projection" d
  ownerDeclaration <- maybe (refuse Syntax "Unknown index projection owner") Right (M.lookup owner (declarations inv))
  sourceParameters <- field inv "parameters" ownerDeclaration >>= number
  unless (get "proper" p == String owner && get "index" p == toJSON (sourceParameters + 1))
    (refuse Syntax "Index projection has wrong owner or parameter count")
  sig <- signature inv d
  let runtimeParameters = sourceParameters - length concrete
      contextual = take runtimeParameters [ix | Runtime _ ix <- args]
  unless (runtimeParameters >= 0 && length contextual == runtimeParameters)
    (refuse Representation "Index projection needs its contextual value parameters")
  out <- instantiate concrete (M.fromList (zip [0..] (contextual ++ [receiver]))) (output sig)
  pure (Runtime out (IndexProject name concrete receiver))
projectIndex _ _ _ = refuse Representation "Index projection requires a record receiver"

parameterKind :: Inventory -> [Maybe Type] -> Value -> Either Refusal (Maybe ParameterKind)
parameterKind inv env ty
  | isLevelType inv ty = Right (Just LevelKind)
  | isUniverse ty = Just . TypeKind <$> readLevel inv env (get "level" (get "sort" (get "term" ty)))
  | get "tag" (get "term" ty) == String "pi" = familyKind env [] ty
  | otherwise = Right Nothing
  where
    familyKind context domains result
      | isUniverse result = Just . FamilyKind domains <$> readLevel inv context (get "level" (get "sort" (get "term" result)))
      | get "tag" (get "term" result) == String "pi" = do
          let term = get "term" result; dom = get "domain" term; cod = get "codomain" term
          -- First-order index domains only. A value-level callback whose
          -- result is not a universe continues through the ordinary refusal.
          case readType inv context (get "term" (get "type" dom)) of
            Left _ -> Right Nothing
            Right Runtime{} -> Right Nothing
            Right domain -> do
              unless (get "relevance" (get "info" dom) == String "relevant" && get "quantity" (get "info" dom) /= String "zero")
                (refuse Semantics "Erased type-family index domain")
              let next = if get "binds" cod == Bool False then context
                    else Just (Runtime domain (IndexFamilyArgument (length domains))):context
              familyKind next (domains ++ [domain]) (get "body" cod)
      | otherwise = Right Nothing
parameterSlot :: Int -> ParameterKind -> Type
parameterSlot _ UnusedKind = Unused
parameterSlot i LevelKind = Level (levelParameter i)
parameterSlot i TypeKind{} = Parameter i
parameterSlot i (FamilyKind domains level) = FamilyParameter i domains level

signature :: Inventory -> Value -> Either Refusal Signature
signature inv d = do
  ty <- field inv "type" d
  p <- field inv "projection" d
  let projectionEnd = case get "proper" p of
        String _ -> Just (get "index" p)
        _ -> Nothing
  (kinds,ins,slots,out) <- go projectionEnd [] [] [] [] ty
  dropCount <- if p == Null then Right 0 else subtract 1 <$> number (get "index" p)
  unless (dropCount >= 0 && dropCount <= length kinds + length ins) (refuse Syntax "Projection-like function drops too many arguments")
  pure (Signature (length kinds) ins out dropCount kinds slots)
  where
    -- A proper projection ends at its record receiver. Remaining Pi binders
    -- belong to the field value, rather than additional projection inputs.
    -- readType then checks the full callable domain, result and independence.
    go projectionEnd env kinds ins slots ty = let t = get "term" ty in
      if get "tag" t == String "pi" && projectionEnd /= Just (toJSON (length kinds + length ins)) then do
      let dom = get "domain" t; cod = get "codomain" t
          extend x = if get "binds" cod == Bool False then env else x:env
      kind <- if toJSON (length slots) `elem` array (get "unusedModuleParameters" d)
        then pure (Just UnusedKind) else parameterKind inv env (get "type" dom)
      -- The owning carrier declares the parameter boundary. A constructor's
      -- first payload can itself be a type/family; it must remain a field.
      let owner = M.findWithDefault d (string (get "family" d)) (declarations inv)
          inHeader = get "kind" d /= String "constructor"
            || length kinds + length ins < either (const 0) id (number (get "parameters" owner))
      case kind of
        Just k | staticKind ins k && inHeader -> go projectionEnd (extend (Just (parameterSlot (length kinds) k)))
          (kinds ++ [k]) ins (slots ++ [TypePosition (length kinds)]) (get "body" cod)
        _ -> do
          let modality = get "info" dom
          unless (get "relevance" modality == String "relevant" && get "quantity" modality /= String "zero")
            (refuse Semantics "Erased or irrelevant value argument requires a separate representation rule")
          a <- readType inv env (get "term" (get "type" dom))
          go projectionEnd (extend (Just (Runtime a (IndexInput (length ins))))) kinds (ins ++ [a])
            (slots ++ [ValuePosition (length ins)]) (get "body" cod)
      else (kinds,ins,slots,) <$> readType inv env t

substituteLevel :: [Type] -> LevelExpr -> Either Refusal LevelExpr
substituteLevel args (LevelExpr n xs) = foldM step (levelConstant n) (M.toAscList xs)
  where
    step total (RigidLevel i,offset) = Right (joinLevel total (shiftLevel offset (openLevel i)))
    step total (BoundLevel i,offset) = do
      actual <- at i args
      case actual of
        Level l -> Right (joinLevel total (shiftLevel offset l))
        _ -> refuse Semantics "Type argument used in a universe-level position"
substitute :: [Type] -> Type -> Either Refusal Type
substitute args = instantiate args M.empty

-- Substitute both template namespaces in one pass. Supplied static arguments
-- and index expressions already belong to the caller; neither may be traversed
-- by the other substitution (a captured callback can itself contain types).
instantiate :: [Type] -> M.Map Int IndexExpr -> Type -> Either Refusal Type
instantiate args values (Callable a b) = Callable <$> traverse (instantiate args values) a <*> instantiate args values b
instantiate args values (SchemaValue ds l) = SchemaValue <$> traverse (instantiate args values) ds <*> substituteLevel args l
instantiate args values (SelectedFamily value) = SelectedFamily <$> instantiate args values value
instantiate _ _ Unused = Right Unused
instantiate args _ (Parameter i) = at i args
instantiate _ _ t@Open{} = Right t
instantiate args _ (FamilyParameter i _ _) = at i args
instantiate args values (OpenFamily i domains level) = OpenFamily i <$> traverse (instantiate args values) domains <*> pure level
instantiate args values (FamilyApplication family indices) = do
  actual <- instantiate args values family
  supplied <- traverse (instantiate args values) indices
  applyTypeFamily actual supplied
instantiate args values (FamilyExpression domain slot body level) = FamilyExpression <$> instantiate args values domain <*> pure slot
  <*> instantiate args values body <*> substituteLevel args level
instantiate args values (Named s ts) = Named s <$> traverse (instantiate args values) ts
instantiate args _ (Level l) = Level <$> substituteLevel args l
instantiate args values (Runtime ty index) = Runtime <$> instantiate args values ty <*> go index
  where
    go (IndexProject f ts receiver) = IndexProject f <$> traverse (instantiate args values) ts <*> go receiver
    go (IndexCall f ts xs) = IndexCall f <$> traverse (instantiate args values) ts <*> traverse go xs
    go (IndexConstructor c ts xs) = IndexConstructor c <$> traverse (instantiate args values) ts <*> traverse go xs
    go (IndexSuccessor i) = IndexSuccessor <$> go i
    go (IndexTyped ty x) = typedIndex <$> instantiate args values ty <*> go x
    go (IndexLambda slots ty x) = IndexLambda slots <$> instantiate args values ty <*> go x
    go (IndexApply f x) = IndexApply <$> go f <*> go x
    go original@(IndexInput i) = Right (M.findWithDefault original i values)
    go i = Right i
closed :: Type -> Bool
closed (Callable a b) = all closed (b:a)
closed (SchemaValue ds l) = all closed ds && closed (Level l)
closed (SelectedFamily value) = closed value
closed Unused = True
closed Parameter{} = False
closed (Open _ level) = closed (Level level)
closed FamilyParameter{} = False
closed (OpenFamily _ domains level) = all closed domains && closed (Level level)
closed (FamilyApplication family indices) = closed family && all closed indices
closed (FamilyExpression domain slot body level) = closed domain && closed (Level level)
  && closed (mapIndices erase body)
  where
    erase (IndexLocal i) | i == slot = IndexCaptured 0
    erase (IndexConstructor c ts xs) = IndexConstructor c (map (mapIndices erase) ts) (map erase xs)
    erase (IndexProject f ts x) = IndexProject f (map (mapIndices erase) ts) (erase x)
    erase (IndexCall f ts xs) = IndexCall f (map (mapIndices erase) ts) (map erase xs)
    erase (IndexSuccessor x) = IndexSuccessor (erase x)
    erase (IndexTyped ty x) = typedIndex (mapIndices erase ty) (erase x)
    erase (IndexLambda slots ty x) = IndexLambda slots (mapIndices erase ty) (erase x)
    erase (IndexApply f x) = IndexApply (erase f) (erase x)
    erase x = x
closed (Runtime ty index) = closed ty && go index
  where
    go IndexCaptured{} = True
    go IndexArgument{} = True
    go IndexFamilyArgument{} = True
    go (IndexTyped ty x) = closed ty && go x
    go (IndexLambda slots ty x) = closed ty && closed (Runtime Unused (bindIndexLocals (zip slots (repeat (IndexCaptured 0))) x))
    go (IndexApply f x) = go f && go x
    go IndexLocal{} = False
    go IndexInput{} = False
    go (IndexConstructor _ args xs) = all closed args && all go xs
    go (IndexProject _ ts receiver) = all closed ts && go receiver
    go (IndexCall _ ts values) = all closed ts && all go values
    go (IndexSuccessor i) = go i
    go IndexNatural{} = True
closed (Named _ ts) = all closed ts
closed (Level (LevelExpr _ xs)) = all rigid (M.keys xs)
  where rigid RigidLevel{} = True; rigid _ = False

-- Read the actual family telescope and result universe, preserving binders
-- even when a parameter is phantom in all runtime fields.
familySignature :: Inventory -> Value -> Either Refusal ([ParameterKind],[Type],LevelExpr)
familySignature inv d = do
  (kinds,ins,level,_) <- familyLayout inv d
  pure (kinds,ins,level)

familyLayout :: Inventory -> Value -> Either Refusal ([ParameterKind],[Type],LevelExpr,[ArgumentSlot])
familyLayout inv d = do
  n <- field inv "parameters" d >>= number
  ty <- field inv "type" d
  go [] [] [] [] n ty
  where
    go env kinds ins slots 0 ty = indices env kinds ins slots ty
    go env kinds ins slots n ty = do
      let t = get "term" ty; cod = get "codomain" t
      unless (get "tag" t == String "pi") (refuse Syntax "Missing carrier parameter telescope")
      kind <- if toJSON (length slots) `elem` array (get "unusedModuleParameters" d)
        then pure (Just UnusedKind) else parameterKind inv env (get "type" (get "domain" t))
      case kind of
        Just k | staticKind ins k -> do
          let extended = if get "binds" cod == Bool False then env else Just (parameterSlot (length kinds) k):env
          go extended (kinds ++ [k]) ins (slots ++ [TypePosition (length kinds)]) (n-1) (get "body" cod)
        _ -> do
          let dom = get "domain" t
          unless (get "relevance" (get "info" dom) == String "relevant"
            && get "quantity" (get "info" dom) /= String "zero") (refuse Semantics "Erased family value parameter")
          a <- readType inv env (get "term" (get "type" dom))
          let extended = if get "binds" cod == Bool False then env else Just (Runtime a (IndexInput (length ins))):env
          go extended kinds (ins ++ [a]) (slots ++ [ValuePosition (length ins)]) (n-1) (get "body" cod)
    indices env kinds ins slots ty
      | isUniverse ty = do
          l <- readLevel inv env (get "level" (get "sort" (get "term" ty)))
          pure (kinds,ins,l,slots)
      | otherwise = do
          let t = get "term" ty; cod = get "codomain" t; dom = get "domain" t
          unless (get "tag" t == String "pi") (refuse Representation "Unsupported carrier universe")
          unless (get "relevance" (get "info" dom) == String "relevant"
            && get "quantity" (get "info" dom) /= String "zero") (refuse Semantics "Erased family index")
          a <- readType inv env (get "term" (get "type" dom))
          let extended = if get "binds" cod == Bool False then env else Just (Runtime a (IndexInput (length ins))):env
          indices extended kinds (ins ++ [a]) (slots ++ [ValuePosition (length ins)]) (get "body" cod)

universeOf :: Inventory -> Type -> Either Refusal LevelExpr
universeOf _ (Open _ level) = Right level
universeOf _ (FamilyApplication (OpenFamily _ _ level) _) = Right level
universeOf _ (FamilyApplication (SelectedFamily (Runtime (SchemaValue _ level) _)) _) = Right level
universeOf inv (SchemaValue domains level) = do
  levels <- traverse (universeOf inv) domains
  pure (foldl joinLevel (shiftLevel 1 level) levels)
universeOf inv (FamilyExpression _ _ body _) = universeOf inv body
universeOf inv (Named s args) = do
  d <- maybe (refuse Syntax "Unknown concrete type universe") Right (M.lookup s (declarations inv))
  (kinds,indices,l) <- familySignature inv d
  unless (length kinds + length indices == length args) (refuse Syntax "Concrete type arity mismatch")
  substituteLevel (staticArguments args) l
universeOf _ _ = refuse Semantics "Static level is not a runtime type"

validateArguments :: Inventory -> [ParameterKind] -> [Type] -> Either Refusal ()
validateArguments inv kinds args = do
  unless (length kinds == length args && all closed args) (refuse Representation "Unresolved static arguments")
  forM_ (zip kinds args) $ \(kind,arg) -> case (kind,arg) of
    (UnusedKind,Unused) -> pure ()
    (LevelKind,Level _) -> pure ()
    (TypeKind expected,t) | case t of Named{} -> True; Open{} -> True; FamilyApplication{} -> True; _ -> False -> do
      actual <- universeOf inv arg
      resolved <- substituteLevel args expected
      unless (actual == resolved) (refuse Semantics "Concrete type argument has the wrong universe")
    (FamilyKind domains level,OpenFamily _ actualDomains actualLevel) -> do
      expectedDomains <- traverse (substitute args) domains
      expectedLevel <- substituteLevel args level
      unless (actualDomains == expectedDomains && actualLevel == expectedLevel)
        (refuse Semantics "Type-family argument has incompatible index domains or universe")
    (FamilyKind domains level,SelectedFamily (Runtime (SchemaValue actualDomains actualLevel) _)) -> do
      expectedDomains <- traverse (substitute args) domains
      expectedLevel <- substituteLevel args level
      unless (actualDomains == expectedDomains && actualLevel == expectedLevel)
        (refuse Semantics "Stored type-family argument has incompatible index domains or universe")
    (FamilyKind domains level,family@FamilyExpression{}) -> do
      expectedDomains <- traverse (substitute args) domains
      expectedLevel <- substituteLevel args level
      let check _ [] body = do
            actual <- universeOf inv body
            unless (expectedLevel == actual) (refuse Semantics "Type-family lambda has incompatible universe")
          check prior (domain:rest) current@(FamilyExpression actualDomain _ _ actualLevel) = do
            let expectedDomain = bindFamilyInputs prior domain
            unless (actualDomain == expectedDomain && actualLevel == expectedLevel)
              (refuse Semantics "Type-family lambda has incompatible domain or universe")
            let value = Runtime expectedDomain (IndexFamilyArgument (length prior))
            body <- applyTypeFamily current [value]
            check (prior ++ [value]) rest body
          check _ _ _ = refuse Semantics "Type-family lambda has incompatible arity"
      check [] expectedDomains family
    _ -> refuse Semantics "Static level/type argument kind mismatch"

-- Solve only a uniquely determined level. Non-injective maxima remain
-- pending until other arguments determine them; no arbitrary level is chosen.
constrainLevel :: M.Map Int Type -> LevelExpr -> Integer -> Either Refusal (M.Map Int Type)
constrainLevel known expected = constrainUniverse known expected . levelConstant

constrainUniverse :: M.Map Int Type -> LevelExpr -> LevelExpr -> Either Refusal (M.Map Int Type)
constrainUniverse known (LevelExpr n xs) target0 = do
  partial <- foldM collect (levelConstant n) (M.toList xs)
  let LevelExpr c remaining = partial
      target@(LevelExpr t atoms) = normalLevel target0
      -- Unknowns belong to the template. Atoms inside an already supplied
      -- level belong to the caller, even if represented by BoundLevel there.
      unknown = [(i,k) | (BoundLevel i,k) <- M.toList xs,M.notMember i known]
      assign i value = Right (M.insert i (Level value) known)
  case unknown of
    [] -> if partial == target then Right known else refuse Semantics "Universe-level mismatch"
    [(i,offset)] | M.null remaining -> case M.null atoms of
      True -> do
        unless (c <= t && offset <= t) (refuse Semantics "Inconsistent universe-level constraint")
        if c < t || offset == t then assign i (levelConstant (t-offset)) else Right known
      False | c <= offset && (t == 0 || t >= offset) && all (>= offset) (M.elems atoms) ->
          assign i (normalLevel (LevelExpr (max 0 (t-offset)) (M.map (subtract offset) atoms)))
      _ -> Right known
    _ | M.null atoms && (c > t || any ((> t) . snd) unknown || any (> t) (M.elems remaining)) ->
          refuse Semantics "Inconsistent universe-level constraint"
      | otherwise -> Right known
  where
    collect total (RigidLevel i,offset) = Right (joinLevel total (shiftLevel offset (openLevel i)))
    collect total (BoundLevel i,offset) = case M.lookup i known of
      Nothing -> Right total
      Just (Level l) -> Right (joinLevel total (shiftLevel offset l))
      _ -> refuse Semantics "Type argument used as a level"

completeKnown :: Inventory -> Signature -> M.Map Int Type -> Either Refusal (M.Map Int Type)
completeKnown inv sig known = do
  next <- foldM step known (zip [0..] (parameterKinds sig))
  if next == known then Right known else completeKnown inv sig next
  where
    step table (i,UnusedKind) = case M.lookup i table of
      Nothing -> Right (M.insert i Unused table)
      Just Unused -> Right table
      _ -> refuse Semantics "Live argument in an unused parameter slot"
    step table (i,TypeKind l) = case M.lookup i table of
      Just t -> universeOf inv t >>= constrainUniverse table l
      Nothing -> Right table
    step table _ = Right table

-- Redundant annotations do not distinguish specialization identities. Binding
-- evidence must nevertheless retain their types: a composed callback's middle
-- domain can occur only in an IndexTyped annotation, yet its native contract
-- still needs that domain's type/family extent in the enclosing scope.
typeValue :: Type -> Value
typeValue = typeValueWith False

bindingTypeValue :: Type -> Value
bindingTypeValue = typeValueWith True

typeValueWith :: Bool -> Type -> Value
typeValueWith retainTypes = value
  where
    value (Callable [a] b) = object ["callableInput" .= value a,"callableResult" .= value b]
    value (Callable as b) = object ["callableInputs" .= map value as,"callableResult" .= value b]
    value (SchemaValue ds l) = object ["schemaDomains" .= map value ds,"schemaUniverse" .= levelValue l]
    value (SelectedFamily ty) = object ["selectedFamily" .= value ty]
    value Unused = object ["unusedModuleParameter" .= True]
    value (Level l) = case levelNumber l of
      Right n -> object ["level" .= n]
      Left _ -> object ["levelExpression" .= levelValue l]
    value (Parameter i) = object ["parameter" .= i]
    value (Open i level) = object ["openParameter" .= i,"universe" .= levelValue level]
    value (FamilyParameter i domains level) = object ["familyParameter" .= i,"domains" .= map value domains,"level" .= value (Level level)]
    value t@(OpenFamily i domains level) = object ["openFamily" .= i,"domains" .= map value domains,"universe" .= levelValue level,"familySymbol" .= typeKey t]
    value (FamilyApplication family indices) = object ["family" .= value family,"indices" .= map value indices]
    value family@FamilyExpression{} = case canonicalFamilies family of
      FamilyExpression domain slot body level -> object ["familyExpression" .= object
        ["domain" .= value domain,"slot" .= slot,"body" .= value body,"level" .= value (Level level)]]
      _ -> Null
    value (Runtime ty ix) = object ["runtimeType" .= value ty,"index" .= index ix]
    value (Named s ts) = object ["symbol" .= s,"arguments" .= map value ts]
    index (IndexInput i) = object ["input" .= i]
    index (IndexCaptured i) = object ["capture" .= i]
    index (IndexLocal i) = object ["familyInput" .= i]
    index (IndexFamilyArgument i) = object ["familyArgument" .= i]
    index (IndexArgument 0) = object ["callbackArgument" .= True]
    index (IndexArgument i) = object ["callbackArgument" .= i]
    index (IndexTyped ty x)
      | retainTypes = object ["indexType" .= value ty,"typedIndex" .= index x]
      | otherwise = index x
    index (IndexLambda slots ty x) = object ["closureInputs" .= slots,"closureType" .= value ty,"body" .= index x]
    index (IndexApply f x) = object ["callback" .= index f,"argument" .= index x]
    index (IndexNatural n) = object ["natural" .= n]
    index (IndexSuccessor i) = object ["successor" .= index i]
    index (IndexConstructor c args values) = object (["constructor" .= c,"arguments" .= map value args]
      ++ ["values" .= map index values | not (null values)])
    index (IndexCall f args values) = object
      ["calculation" .= f,"arguments" .= map value args,"values" .= map index values]
    index (IndexProject f args receiver) = object
      ["projection" .= f,"arguments" .= map value args,"receiver" .= index receiver]
instanceKey :: Text -> [Type] -> Text
instanceKey s [] = s
instanceKey s ts = s <> "@" <> digest (BL.toStrict (encode (object ["symbol" .= s,"arguments" .= map typeValue (fst (captureArguments ts))])))
typeKey :: Type -> Text
typeKey ty@Callable{} = "$native-callable:" <> digest (BL.toStrict (encode (typeValue ty)))
typeKey ty@SchemaValue{} = "$native-schema:" <> digest (BL.toStrict (encode (typeValue canonical)))
  where canonical = case fst (captureArguments [ty]) of [value] -> value; _ -> ty
typeKey (SelectedFamily (Runtime schema _)) = typeKey schema <> ".member"
typeKey SelectedFamily{} = "$invalid-stored-schema"
typeKey Unused = "$unused-module-parameter"
typeKey (Named s ts) = instanceKey s (staticArguments ts)
typeKey (Level l) = "level:" <> levelKey l
typeKey Runtime{} = "runtime-index-has-no-static-key"
typeKey (Parameter i) = "unresolved-parameter-" <> T.pack (show i)
typeKey (Open i level) = "$native-type-parameter:" <> T.pack (show i) <> ":" <> levelKey level
typeKey (FamilyParameter i _ _) = "unresolved-family-" <> T.pack (show i)
typeKey (OpenFamily i domains level) = "$native-type-family:" <> T.pack (show i) <> ":"
  <> digest (BL.toStrict (encode (map typeValue domains,levelValue level)))
typeKey (FamilyApplication family _) = typeKey family
typeKey family@FamilyExpression{} = "$native-family-expression:" <> digest (BL.toStrict (encode (typeValue family)))

levelKey :: LevelExpr -> Text
levelKey l = either (const (digest (BL.toStrict (encode (levelValue l))))) (T.pack . show) (levelNumber l)

-- Parameters remain distinct even when two native classifiers have equal
-- extents. These slots are local to a calculation/container, not global types.
nativeParameters :: Value -> [Int]
nativeParameters d = S.toAscList (slots (get "specializationArguments" d)
  `S.union` slots (get "types" (get "closureSpecialization" d)))
  where
    slots (Object o) = case KM.lookup "openParameter" o of
      Just v -> either (const S.empty) S.singleton (number v)
      Nothing -> S.unions (map slots (KM.elems o))
    slots (Array xs) = S.unions (map slots (foldr (:) [] xs))
    slots _ = S.empty

nativeFamilies :: Value -> [(Int,Text)]
nativeFamilies d = M.toAscList (families (get "specializationArguments" d)
  `M.union` families (get "types" (get "closureSpecialization" d)))
  where
    families (Object o) = let children = M.unions (map families (KM.elems o)) in
      case (KM.lookup "openFamily" o,KM.lookup "familySymbol" o) of
        (Just i,Just (String s)) -> either (const children) (\slot -> M.insert slot s children) (number i)
        _ -> children
    families (Array xs) = M.unions (map families (foldr (:) [] xs))
    families _ = M.empty

typeTerm :: Int -> Type -> Value
typeTerm depth (Callable domains out) = object ["tag" .= ("native-callable" :: Text)
  ,"inputs" .= [asType (depth+i) (applyCallback positions domain) | (i,domain) <- zip [0..] domains]
  ,"result" .= asType (depth+length domains) (applyCallback positions out)]
  where positions = map IndexInput [depth..depth+length domains-1]
typeTerm depth ty@(Named _ args) = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty
  ,"eliminations" .= [application (indexTerm depth i) | i <- map snd (snd (captureArguments (staticArguments args))) ++ [ix | Runtime _ ix <- args]]]
typeTerm depth ty@(FamilyApplication _ args) = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty
  ,"eliminations" .= [application (indexTerm depth i) | Runtime _ i <- familyArguments ty args]]
typeTerm depth ty@SchemaValue{} = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty
  ,"eliminations" .= [application (indexTerm depth i) | (_,i) <- snd (captureArguments [ty])]]
typeTerm _ ty = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty,"eliminations" .= ([] :: [Value])]

familyArguments :: Type -> [Type] -> [Type]
familyArguments (FamilyApplication (SelectedFamily value@(Runtime schema _)) _) args =
  [Runtime domain index | (domain,index) <- snd (captureArguments [schema])] ++ value:args
familyArguments _ args = args
indexTerm :: Int -> IndexExpr -> Value
indexTerm depth (IndexCaptured i) = indexTerm depth (IndexInput i)
indexTerm _ (IndexLocal _) = object ["tag" .= ("unbound-family-input" :: Text)]
indexTerm _ (IndexFamilyArgument i) = object ["tag" .= ("native-family-input" :: Text),"index" .= i]
indexTerm _ IndexArgument{} = object ["tag" .= ("unbound-callback-input" :: Text)]
indexTerm depth (IndexTyped _ x) = indexTerm depth x
indexTerm depth (IndexLambda slots (Callable domains out) body) = object
  ["tag" .= ("native-lambda" :: Text)
  ,"inputs" .= [asType (depth+i) (applyCallback positions domain) | (i,domain) <- zip [0..] domains]
  ,"result" .= asType (depth+length slots) (applyCallback positions out)
  ,"body" .= indexTerm (depth+length slots) (bindIndexLocals (zip slots positions) body)]
  where positions = map IndexInput [depth..depth+length slots-1]
indexTerm _ IndexLambda{} = object ["tag" .= ("invalid-index-closure" :: Text)]
indexTerm depth (IndexApply f x) = let t = indexTerm depth f in
  set "eliminations" (toJSON (array (get "eliminations" t) ++ [application (indexTerm depth x)])) t
indexTerm depth (IndexInput i) = object ["tag" .= ("variable" :: Text),"index" .= (depth-i-1),"eliminations" .= ([] :: [Value])]
indexTerm _ (IndexNatural n) = object ["tag" .= ("literal" :: Text),"literal" .= object ["tag" .= ("natural" :: Text),"value" .= n]]
indexTerm depth (IndexSuccessor i) = object ["tag" .= ("native-index-successor" :: Text),"predecessor" .= indexTerm depth i]
indexTerm depth (IndexConstructor c args values) = object ["tag" .= ("constructor" :: Text),"symbol" .= instanceKey c args
  ,"nativeIndexCaptures" .= map (indexTerm depth . snd) (snd (captureArguments args))
  ,"eliminations" .= map (application . indexTerm depth) values]
indexTerm depth (IndexCall f args values) = object ["tag" .= ("definition" :: Text),"symbol" .= instanceKey f args
  ,"nativeFullArguments" .= True
  ,"eliminations" .= map (application . indexTerm depth) (map snd (snd (captureArguments args)) ++ values)]
indexTerm depth (IndexProject f args receiver) = let t = indexTerm depth receiver in
  set "eliminations" (toJSON (array (get "eliminations" t) ++
    [object ["tag" .= ("project" :: Text),"symbol" .= instanceKey f args]])) t
asType :: Int -> Type -> Value
asType depth ty = object ["term" .= typeTerm depth ty]
info :: Value
info = object ["relevance" .= ("relevant" :: Text),"quantity" .= ("unrestricted" :: Text),"hiding" .= ("explicit" :: Text)]
arrow :: [Type] -> Type -> Value
arrow ins out = telescope ins (asType (length ins) out)
telescope :: [Type] -> Value -> Value
telescope = go 0
  where
    go _ [] out = out
    go depth (x:xs) out = object ["term" .= object ["tag" .= ("pi" :: Text)
      ,"domain" .= object ["info" .= info,"type" .= asType depth x]
      ,"codomain" .= object ["binds" .= True,"name" .= ("_" :: Text),"body" .= go (depth+1) xs out]]]

application :: Value -> Value
application x = object ["tag" .= ("apply" :: Text),"argument" .= object ["info" .= info,"value" .= x]]

prepare :: Inventory -> Result
prepare source | not active = Result source [] M.empty roots S.empty M.empty M.empty M.empty
            | otherwise = Result expanded entries errors roots runtime open statements statementNeeds
  where
    inv = UnusedParameters.annotate source
    needs = required inv
    active = not (null statementSeeds) || any (\(s,r) -> r `elem` ["structure","behavior"] && generic s
      || r == "behavior" && callbackSignature s
      || r == "structure" && moduleConstructor s
      || r == "structure" && moduleCarrier s
      || r `elem` ["structure","behavior"] && moduleProjection s) (S.toList needs)
    moduleConstructor s = maybe False (\d -> get "kind" d == String "constructor"
      && get "moduleInstanceCopy" d == Bool True) (M.lookup s (declarations inv))
    moduleCarrier s = maybe False (\d -> get "kind" d `elem` map String ["record","datatype"]
      && get "moduleInstanceCopy" d == Bool True) (M.lookup s (declarations inv))
    moduleProjection s = maybe False (\d -> get "kind" d == String "function"
      && get "moduleInstanceCopy" d == Bool True
      && either (const False) ((/= Null) . get "proper") (field inv "projection" d)) (M.lookup s (declarations inv))
    statementSeeds = [s | (s,"statement") <- S.toAscList needs
      ,Just d <- [M.lookup s (declarations inv)],get "kind" d == String "function"
      ,Right ty <- [field inv "type" d],equalityResult ty]
    equalityResult ty = let t = get "term" ty in
      if get "tag" t == String "pi" then equalityResult (get "body" (get "codomain" t))
      else not (T.null (builtin inv "equality")) && get "tag" t == String "definition"
        && get "symbol" t == String (builtin inv "equality")
    callbackSignature s = case M.lookup s (declarations inv) >>= either (const Nothing) Just . field inv "type" of
      Just ty -> callableDomains S.empty ty
      Nothing -> False
    callableDomains seen ty = let t = get "term" ty in
      get "tag" t == String "pi" &&
        (callableCarrier seen (get "term" (get "type" (get "domain" t)))
          || callableDomains seen (get "body" (get "codomain" t)))
    callableCarrier seen term
      | get "tag" term == String "pi" = True
      | get "tag" term == String "definition" =
          let name = string (get "symbol" term) in not (S.member name seen) && case M.lookup name (declarations inv) of
            Just d | get "kind" d `elem` [String "record",String "datatype"] ->
              let sourceField k = either (const Null) id (field inv k d)
                  constructors = if get "kind" d == String "record" then [string (sourceField "constructor")]
                    else map string (array (sourceField "constructors"))
              in any (\c -> case M.lookup c (declarations inv) >>= either (const Nothing) Just . field inv "type" of
                Just ty -> callableDomains (S.insert name seen) ty
                Nothing -> False) constructors
            _ -> maybe False (callableCarrier (S.insert name seen) . fst) (Reduction.reduceHead inv term)
      | otherwise = False
    generic s = case M.lookup s (declarations inv) of
      Nothing -> False
      Just d -> case field inv "type" d of
        Right ty -> get "tag" (get "term" ty) == String "pi" &&
          (Number 0 `elem` array (get "unusedModuleParameters" d) || case parameterKind inv [] (get "type" (get "domain" (get "term" ty))) of
            Right (Just _) -> True
            _ -> lateStatic ty)
        _ -> False
    lateStatic ty = let t = get "term" ty in get "tag" t == String "pi" &&
      (isUniverse (get "type" (get "domain" t)) || isLevelType inv (get "type" (get "domain" t))
        || lateStatic (get "body" (get "codomain" t)))
    seeds = S.toAscList (S.map fst (S.filter (\(_,r) -> r `elem` ["structure","behavior"]) needs))
    openProfile = get "selectionProfile" (document inv) == String "declarations"
    action = forM seeds $ \s -> if generic s && not (openProfile && S.member s roots) then pure (s,Right s) else do
      before <- gets id
      result <- runExceptT $ do
        d <- definition inv s
        args <- if not (generic s) then pure [] else do
          kinds <- if get "kind" d `elem` [String "record",String "datatype"]
            then (\(ks,_,_) -> ks) <$> liftEither (familySignature inv d)
            else parameterKinds <$> liftEither (signature inv d)
          foldM (\prior (i,k) -> do
            arg <- case k of
              UnusedKind -> pure Unused
              TypeKind level -> Open i <$> liftEither (substituteLevel prior level)
              FamilyKind domains level -> OpenFamily i <$> liftEither (traverse (substitute prior) domains)
                <*> liftEither (substituteLevel prior level)
              LevelKind -> pure (Level (openLevel i))
            pure (prior ++ [arg])) [] (zip [0..] kinds)
        if moduleConstructor s then ensureConstructorRoot inv s args
        else if moduleCarrier s then ensureCarrierRoot inv s args
        else if moduleProjection s then ensureProjectionRoot inv s args else do
          case string (get "kind" d) of
            "record" -> ensureType inv [] (Named s args)
            "datatype" -> do
              ty <- liftEither (field inv "type" d)
              -- Indexed relations keep their separate existing lowering rule.
              when (generic s || get "tag" (get "term" ty) == String "sort") (ensureType inv [] (Named s args))
            "function" -> do
              alias <- liftEither (typeAlias inv d)
              case alias of
                Just ty -> ensureType inv [] ty
                Nothing -> do
                  p <- liftEither (field inv "projection" d)
                  case get "proper" p of
                    String owner -> ensureType inv [] (Named owner args)
                    _ -> ensureFunction inv [] s args
            _ -> pure ()
          pure (instanceKey s args)
      case result of Left _ -> modify' (const before); Right _ -> pure ()
      pure (s,result)
    -- Statement preparation checks the telescope and its index computations,
    -- never the proof implementation. Failed attempts leave runtime preparation
    -- intact. Target admission decides which optional statement dependencies
    -- enter the emitted scope.
    statementAction = forM statementSeeds $ \s -> do
      before <- gets id
      outcome <- runExceptT $ do
        d <- definition inv s
        sig <- liftEither (signature inv d)
        args <- foldM (\prior (i,k) -> do
          arg <- case k of
            UnusedKind -> pure Unused
            TypeKind level -> Open i <$> liftEither (substituteLevel prior level)
            FamilyKind domains level -> OpenFamily i <$> liftEither (traverse (substitute prior) domains)
              <*> liftEither (substituteLevel prior level)
            LevelKind -> pure (Level (openLevel i))
          pure (prior ++ [arg])) [] (zip [0..] (parameterKinds sig))
        ins <- liftEither (traverse (substitute args) (inputs sig))
        out <- liftEither (substitute args (output sig))
        mapM_ (ensureType inv []) (out:ins)
        let key = instanceKey (s <> ".statement") args
            statement = set "name" (String key) $ set "kind" (String "native-equality-statement")
              $ set "displayName" (String (display inv s <> ".law" <> if null args then "" else suffix inv args))
              $ set "statementOrigin" (String s) $ set "specializationOrigin" (String s)
              $ set "preparationOrigin" (String s) $ set "specializationArguments" (toJSON (map bindingTypeValue args))
              $ set "type" (arrow ins out) $ set "compiled" Null d
        when (M.member key (declarations inv)) (abort Syntax "Statement identity collides with checked source")
        modify' $ \st -> st {ready = M.insert key statement (ready st)}
        pure key
      case outcome of Left _ -> modify' (const before); Right _ -> pure ()
      pure (s,outcome)
    ((attempts,statementAttempts),store) = runState ((,) <$> action <*> statementAction) (Store M.empty M.empty)
    statements = M.fromList statementAttempts
    statementNeeds = M.fromList [(s,statementClosure key) | (s,Right key) <- statementAttempts]
      where
        statementClosure key =
          let names = reach S.empty [key]
              invoked = S.unions [either (const S.empty) callsIn (field inv root d)
                | name <- S.toList names,Just d <- [M.lookup name (ready store)]
                ,root <- ["type","compiled","closureIndexEquations"]]
          in S.fromList [(name,role invoked name d)
            | name <- S.toList names,Just d <- [M.lookup name (ready store)]
            ,get "kind" d `elem` map String ["function","primitive","record","datatype","constructor"]]
        -- A field is structural evidence. Projection eliminations read that
        -- field directly; only a definition application needs its calculation.
        role invoked name d
          | get "proper" (get "projection" d) /= Null, S.notMember name invoked = "structure"
          | get "kind" d `elem` map String ["function","primitive"] = "behavior"
          | otherwise = "structure"
        callsIn value@(Object fields) = S.unions (map callsIn (KM.elems fields)) `S.union`
          (if get "tag" value == String "definition" then S.singleton (string (get "symbol" value)) else S.empty)
        callsIn (Array values) = S.unions (map callsIn (foldr (:) [] values))
        callsIn _ = S.empty
    errors = M.fromList [(s,e) | (s,Left e) <- attempts]
    open = M.fromList [(s,key) | (s,Right key) <- attempts,generic s || key /= s,openProfile,S.member s roots]
    entries = M.elems (recorded store)
    -- Follow the specialized semantic graph separately for each model. Two
    -- models using one template at different types must not acquire each
    -- other's concrete obligations merely because the source symbol matches.
    semanticFields = ["type","compiled","constructors","constructor","fields","projection","closureIndexEquations"]
    refs (String s) = S.singleton s
    refs (Object o) = S.unions (map refs (KM.elems o))
    refs (Array xs) = S.unions (map refs (foldr (:) [] xs))
    refs _ = S.empty
    edges s = maybe S.empty (\d -> S.unions
      [either (const S.empty) refs (field inv k d) | k <- semanticFields]) (M.lookup s (ready store))
      `S.union` maybe S.empty (S.fromList . map typeKey . arguments) (M.lookup s (recorded store))
    reach seen [] = seen
    reach seen (s:ss) | S.member s seen = reach seen ss
                     | otherwise = reach (S.insert s seen) (S.toList (edges s) ++ ss)
    extra ns = let reached = reach S.empty [M.findWithDefault s s open | (s,r) <- S.toList ns,r `elem` ["structure","behavior"]] in
      S.fromList [(identity i,r) | i <- entries,S.member (identity i) reached
        ,(s,r) <- S.toList ns,origin i == s,r `elem` ["structure","behavior"]]
      `S.union` S.fromList [(key,r) | (s,r) <- S.toList ns,r `elem` ["structure","behavior"]
        ,Just key <- [M.lookup s open]]
    expanded = inv { declarations = M.union (ready store) (declarations inv)
      ,modelRequirements = M.map (\ns -> ns `S.union` extra ns) (modelRequirements inv) }
    models = case get "models" (document inv) of Object ms -> KM.elems ms; _ -> []
    runtimeRoots = S.map (\s -> M.findWithDefault s s open) roots
    runtime = if S.null runtimeRoots || not (runtimeRoots `S.isSubsetOf` M.keysSet (ready store)) then S.empty
      else runtimeReach S.empty (S.toList runtimeRoots)
    runtimeReach seen [] = seen
    runtimeReach seen (s:ss) | S.member s seen = runtimeReach seen ss
      | otherwise = runtimeReach (S.insert s seen) (S.toList (runtimeEdges s) ++ ss)
    runtimeEdges s = maybe S.empty (\d -> S.unions
      [either (const S.empty) runtimeRefs (field inv k d)
       | k <- if get "proper" (get "projection" d) /= Null then filter (/= "compiled") semanticFields else semanticFields])
      (M.lookup s (declarations expanded))
    runtimeRefs (String s) = if M.member s (declarations expanded) then S.singleton s else S.empty
    runtimeRefs (Object fields) = S.unions [runtimeRefs x | (k,x) <- KM.toList fields
      ,k `notElem` ["$occurrence","reductionEvidence"]]
    runtimeRefs (Array xs) = S.unions (map runtimeRefs (foldr (:) [] xs))
    runtimeRefs _ = S.empty
    roots = if get "selectionProfile" (document inv) == String "declarations" then
      S.fromList [s | (s,role) <- S.toList needs,role `elem` ["structure","behavior"],S.member s (projectSymbols inv)]
      else S.fromList [string s | m <- models
      ,let result = get "result" (get "transition" m)
      ,ref <- [get "state" m,get "commands" m,get "entry" (get "transition" m)
        ,get "family" result,get "projection" result]
        ++ map (get "predicate") (array (get "invariants" m))
        ++ map (get "constructor") (array (get "variants" result))
      ,s <- array (get "symbols" ref)]

definition :: Inventory -> Text -> Build Value
definition inv s = maybe (abort Syntax ("Missing checked declaration: " <> s)) pure (M.lookup s (declarations inv))
showType :: Inventory -> Type -> Text
showType inv (Callable a b) = "(" <> T.intercalate " → " (map (showType inv) (a ++ [b])) <> ")"
showType _ schema@SchemaValue{} = "stored schema " <> T.takeEnd 12 (typeKey schema)
showType inv (SelectedFamily value) = "member of " <> showType inv value
showType _ Unused = "unused module parameter"
showType _ (Level (LevelExpr n xs)) = "level " <> case terms of
    [term] -> term
    _ -> "max(" <> T.intercalate ", " terms <> ")"
  where
    terms = [T.pack (show n) | n > 0 || M.null xs] ++
      [name atom <> if offset == 0 then "" else "+" <> T.pack (show offset) | (atom,offset) <- M.toAscList xs]
    name (BoundLevel i) = "parameter " <> T.pack (show i)
    name (RigidLevel i) = "ℓ" <> T.pack (show i)
showType inv (Runtime _ index) = showIndex index
  where
    showIndex (IndexCaptured i) = "captured index " <> T.pack (show i)
    showIndex (IndexLocal i) = "family input " <> T.pack (show i)
    showIndex (IndexFamilyArgument i) = "family argument " <> T.pack (show i)
    showIndex (IndexInput i) = "input" <> T.pack (show i)
    showIndex (IndexArgument i) = "argument" <> if i == 0 then "" else T.pack (show i)
    showIndex (IndexTyped _ x) = showIndex x
    showIndex (IndexLambda _ _ x) = "lambda(" <> showIndex x <> ")"
    showIndex (IndexApply f x) = showIndex f <> "(" <> showIndex x <> ")"
    showIndex (IndexNatural n) = T.pack (show n)
    showIndex (IndexSuccessor i) = "suc(" <> showIndex i <> ")"
    showIndex (IndexConstructor c args values) = display inv c <> suffix inv args
      <> (if null values then "" else "(" <> T.intercalate ", " (map showIndex values) <> ")")
    showIndex (IndexCall f args values) = display inv f <> suffix inv args <> "(" <> T.intercalate ", " (map showIndex values) <> ")"
    showIndex (IndexProject f args receiver) = "(" <> showIndex receiver <> ")." <> display inv f <> suffix inv args
showType _ (Parameter i) = "?" <> T.pack (show i)
showType _ (Open i _) = "type parameter " <> T.pack (show i)
showType _ (FamilyParameter i _ _) = "family parameter " <> T.pack (show i)
showType _ (OpenFamily i _ _) = "type family " <> T.pack (show i)
showType inv (FamilyApplication family args) = showType inv family <> suffix inv args
showType inv (FamilyExpression domain _ body _) = "family (" <> showType inv domain <> " → " <> showType inv body <> ")"
showType inv (Named s args) = display inv s <> suffix inv args
display :: Inventory -> Text -> Text
display inv s = maybe s (string . get "displayName") (M.lookup s (declarations inv))
suffix :: Inventory -> [Type] -> Text
suffix _ [] = ""
suffix inv ts = "<" <> T.intercalate ", " (map (showType inv) ts) <> ">"
clone :: Inventory -> Text -> [Type] -> Value -> Value
clone inv s args d = set "name" (String (instanceKey s args))
  $ set "displayName" (String (display inv s <> suffix inv args))
  $ if null args then d else set "specializationOrigin" (String s) d
save :: Text -> [Type] -> Value -> Build ()
save s args d = do
  let key = instanceKey s args
      source = case get "higherOrderOrigin" d of String original -> original; _ -> s
      item = Instance source (fst (captureArguments args)) key
  old <- gets (M.lookup key . recorded)
  unless (maybe True (== item) old) (abort Syntax "Specialization identity collision")
  modify' $ \st -> st {ready = M.insert key (set "preparationOrigin" (String source)
      $ set "specializationArguments" (toJSON (map bindingTypeValue (fst (captureArguments args)))) d) (ready st)
    ,recorded = if null args && source == s then recorded st else M.insert key item (recorded st)}

cached :: Inventory -> Text -> [Type] -> Build Bool
cached inv s args = do
  let key = instanceKey s args
  unless (null args || not (M.member key (declarations inv))) (abort Syntax "Specialization collides with checked source identity")
  exists <- gets (M.member key . ready)
  when (exists && not (null args)) $ do
    prior <- gets (M.lookup key . recorded)
    unless (prior == Just (Instance s (fst (captureArguments args)) key)) (abort Syntax "Specialization identity collision")
  pure exists

ensureType :: Inventory -> [Text] -> Type -> Build ()
ensureType inv stack (Callable a b) = mapM_ (ensureType inv stack) (b:a)
ensureType inv stack (SelectedFamily (Runtime schema index)) = ensureType inv stack schema >> ensureIndex inv index
ensureType _ _ SelectedFamily{} = abort Semantics "Stored family lacks its schema value"
ensureType inv stack schema@(SchemaValue domains level) = do
  let ([SchemaValue canonicalDomains _],captures) = captureArguments [schema]
      captureTypes = map (materializeCaptures . fst) captures
      prefix = length captures
      contextualDomains = materializeFamilyDomains prefix (map materializeCaptures canonicalDomains)
      key = typeKey schema
  unless (all closed canonicalDomains && all firstOrder domains && closed (Level level))
    (abort Representation "Stored schema needs bound first-order index domains")
  mapM_ (ensureType inv stack) (captureTypes ++ contextualDomains)
  forM_ [(key,"binding"),(key <> ".row","row"),(key <> ".member","member")] $ \(symbol,kind) -> do
    when (M.member symbol (declarations inv)) (abort Syntax "Native schema identity collides with a source declaration")
    modify' $ \st -> st {ready = M.insert symbol (object
      ["name" .= symbol,"displayName" .= (showType inv schema <> "." <> kind),"kind" .= ("native-schema-value" :: Text)
      ,"nativeSchema" .= kind,"schemaBinding" .= key,"schemaDomains" .= zipWith asType [prefix..] contextualDomains
      ,"schemaCaptures" .= [asType i domain | (i,domain) <- zip [0..] captureTypes]
      ,"specializationArguments" .= [bindingTypeValue (SchemaValue canonicalDomains level)],"universe" .= levelValue level]) (ready st)}
  where
    firstOrder Callable{} = False
    firstOrder Runtime{} = False
    firstOrder _ = True
ensureType _ _ Unused = abort Semantics "Unused module parameter used as a runtime carrier"
ensureType _ _ Level{} = abort Semantics "Universe level cannot be a runtime carrier"
ensureType _ _ Runtime{} = abort Semantics "Runtime index cannot be a static carrier"
ensureType _ _ Parameter{} = abort Representation "Unresolved type parameter"
ensureType _ _ FamilyParameter{} = abort Representation "Unresolved type-family parameter"
ensureType inv stack (FamilyApplication family args) = do
  ensureType inv stack family
  forM_ args $ \arg -> case arg of
    Runtime domain index -> ensureType inv stack domain >> ensureIndex inv index
    _ -> abort Representation "Type-family index is not a checked value"
ensureType inv stack (FamilyExpression domain _ body _) = do
  ensureType inv stack domain
  ensureBindings body
  where
    ensureBindings t@Open{} = ensureType inv stack t
    ensureBindings t@OpenFamily{} = ensureType inv stack t
    ensureBindings (Named _ xs) = mapM_ ensureBindings xs
    ensureBindings (FamilyApplication f xs) = mapM_ ensureBindings (f:xs)
    ensureBindings (FamilyExpression d _ b _) = ensureBindings d >> ensureBindings b
    ensureBindings (Runtime t _) = ensureBindings t
    ensureBindings _ = pure ()
ensureType inv stack family@(OpenFamily slot domains level) = do
  let key = typeKey family
      contextualDomains = materializeFamilyDomains 0 domains
  when (M.member key (declarations inv)) (abort Syntax "Native family identity collides with a source declaration")
  unless (not (null domains) && all closed domains) (abort Representation "Type-family domains must be bound first-order carriers")
  mapM_ (ensureType inv stack) contextualDomains
  modify' $ \st -> st {ready = M.insert key (object ["name" .= key,"displayName" .= ("type family " <> T.pack (show slot))
    ,"kind" .= ("native-family-parameter" :: Text),"nativeFamily" .= slot,"familyDomains" .= zipWith asType [0..] contextualDomains
    ,"specializationArguments" .= [bindingTypeValue family],"universe" .= levelValue level]) (ready st)}
ensureType inv _ ty@(Open i level) = do
  let key = typeKey ty
  when (M.member key (declarations inv)) (abort Syntax "Native parameter identity collides with a source declaration")
  modify' $ \st -> st {ready = M.insert key (object ["name" .= key
    ,"kind" .= ("native-type-parameter" :: Text),"nativeParameter" .= i,"universe" .= levelValue level]) (ready st)}
ensureType inv _ (Named s []) | s == builtin inv "nat" && not (T.null s) = do
  d <- definition inv s
  save s [] d
  forM_ [builtin inv "zero",builtin inv "suc"] $ \c -> definition inv c >>= save c []
ensureType inv stack ty@(Named s args) | s == builtin inv "list" && not (T.null s) && null (snd (captureArguments args)) = do
  exists <- cached inv s args
  unless exists $ do
    d <- definition inv s
    (kinds,indices,_) <- liftEither (familySignature inv d)
    liftEither (validateArguments inv kinds args)
    element <- case args of
      [Level{},t] | null indices && (case t of Named{} -> True; Open{} -> True; _ -> False) -> pure t
      _ -> abort Representation "List requires a bound level and element type"
    ensureType inv stack element
    let nil = builtin inv "nil"; cons = builtin inv "cons"
    cs <- map string . array <$> liftEither (field inv "constructors" d)
    unless (cs == [nil,cons] && all (not . T.null) cs) (abort Semantics "Builtin list constructor identity mismatch")
    forM_ [(nil,[]),(cons,[element,ty])] $ \(c,expectedInputs) -> do
      cd <- definition inv c
      sig <- liftEither (signature inv cd)
      ins <- liftEither (traverse (substitute args) (inputs sig))
      out <- liftEither (substitute args (output sig))
      unless (parameters sig == length args && ins == expectedInputs && out == ty)
        (abort Semantics "Builtin list constructor schema mismatch")
      save c args $ set "type" (arrow ins out) $ set "parameters" (Number 0)
        $ set "family" (String (typeKey ty)) $ clone inv c args cd
    save s args $ set "nativeSequence" (asType 0 element)
      $ set "type" (object ["term" .= object ["tag" .= ("sort" :: Text)]])
      $ set "parameters" (Number 0) $ set "constructors" (toJSON (map (`instanceKey` args) cs)) $ clone inv s args d
ensureType inv stack ty@(Named s allArgs) = do
  let (args,captures) = captureArguments (staticArguments allArgs)
      schemaArgs = map materializeCaptures args
      captureTypes = map (materializeCaptures . fst) captures
      prefix = length captures
      instantiate sourceType = substitute schemaArgs (shiftIndices prefix sourceType)
  unless (all closed args) (abort Representation "Carrier specialization requires concrete static arguments")
  forM_ (staticArguments allArgs) $ \arg -> case arg of Level{} -> pure (); Unused -> pure (); _ -> ensureType inv stack arg
  forM_ (drop (length args) allArgs) $ \arg -> case arg of
    Runtime domain index -> ensureType inv stack domain >> ensureIndex inv index
    _ -> abort Representation "Static argument follows a runtime family index"
  exists <- cached inv s args
  when (exists && instanceKey s args `elem` stack) $ do
    original <- definition inv s
    unless (inductiveChecked inv original) (abort Semantics "Recursive carrier lacks safe inductive positivity evidence")
  unless exists $ do
    d <- definition inv s
    when (length stack >= 128) (abort Representation "Carrier specialization depth exhausted")
    when (any (\key -> key == s || (s <> "@") `T.isPrefixOf` key) stack
      && not (nonRecursiveTemplate inv s)) (abort Semantics ("Recursive carrier family: " <> s))
    unless (get "kind" d `elem` [String "record",String "datatype"]) (abort Representation "Type argument is not a checked algebraic carrier")
    sourceParameters <- liftEither (field inv "parameters" d >>= number)
    (kinds,indices,_) <- liftEither (familySignature inv d)
    let n = length kinds
    unless (n == length args) (abort Syntax "Carrier parameter arity mismatch")
    indexTypes <- liftEither ((\xs -> captureTypes ++ xs) <$> traverse instantiate indices)
    let contexts = [i | (i,Callable{}) <- zip [0 :: Int ..] (take (prefix+sourceParameters-n) indexTypes)]
    mapM_ (ensureType inv (instanceKey s args:stack)) indexTypes
    liftEither (validateArguments inv kinds args)
    cs <- if get "kind" d == String "record" then (:[]) . string <$> liftEither (field inv "constructor" d)
      else map string . array <$> liftEither (field inv "constructors" d)
    fields <- map string . array <$> liftEither (field inv "fields" d)
    let captureFields = [typeKey ty <> ".capture" <> T.pack (show i) | i <- [0..prefix-1]]
        runtimeCount = sourceParameters-n
        parameterFields = [typeKey ty <> ".parameter" <> T.pack (show i) | i <- [0..runtimeCount-1]]
        recordPrefix = prefix+runtimeCount
        prefixFields = captureFields ++ parameterFields
        nativeFields = prefixFields ++ map (`instanceKey` args) fields
    -- A header permits only the same static instance to recur. Every payload
    -- is still checked before this provisional declaration becomes usable.
    let header = set "nativeContextIndices" (toJSON contexts) $ set "type" (telescope indexTypes (object ["term" .= object ["tag" .= ("sort" :: Text)]]))
          $ set "parameters" (Number 0) $ set "fields" (toJSON nativeFields)
          $ set "nativeRecordCaptures" (toJSON (if get "kind" d == String "record" then recordPrefix else 0))
          $ (case (get "kind" d,cs) of
              (String "record",[c]) -> set "constructor" (String (instanceKey c args))
              _ -> set "constructors" (toJSON (map (`instanceKey` args) cs))) $ clone inv s args d
    save s args header
    cdefs <- forM cs $ \c -> do
      cd <- definition inv c
      sig <- liftEither (signature inv cd)
      unless (parameters sig == n) (abort Syntax "Constructor parameter telescope mismatch")
      ins <- liftEither ((\xs -> captureTypes ++ xs) <$> traverse instantiate (inputs sig))
      out <- liftEither (instantiate (output sig))
      unless (typeKey out == typeKey ty && case out of
        Named _ xs -> length xs == n + length indices; _ -> False)
        (abort Semantics ("Constructor result has wrong family or index arity: " <> typeKey out <> " /= " <> typeKey ty))
      mapM_ (ensureType inv (instanceKey s args:stack)) ins
      case out of
        Named _ xs -> mapM_ (\x -> case x of Runtime _ i -> ensureIndex inv i; _ -> pure ()) xs
        _ -> pure ()
      let cd' = set "type" (arrow ins out) $ set "parameters" (Number 0)
            $ set "runtimeParameters" (toJSON (if get "kind" d == String "record" then 0 else runtimeCount+prefix))
            $ set "patternCaptures" (toJSON (if get "kind" d == String "record" then recordPrefix else 0))
            $ set "family" (String (typeKey ty)) $ clone inv c args cd
      save c args cd'
      pure (ins,cd')
    when (get "kind" d == String "record") $ case cdefs of
      [(ins,_)] -> do
        unless (length nativeFields == length ins) (abort Syntax "Record constructor/field arity mismatch")
        let receiver = Named (typeKey ty) []
            rebaseIndex (IndexInput i) | i < recordPrefix = IndexProject (prefixFields !! i) [] (IndexInput 0)
                                      | i == recordPrefix = IndexInput 0
            rebaseIndex (IndexProject f ts x) = IndexProject f (map (mapIndices rebaseIndex) ts) (rebaseIndex x)
            rebaseIndex (IndexConstructor c ts xs) = IndexConstructor c (map (mapIndices rebaseIndex) ts) (map rebaseIndex xs)
            rebaseIndex (IndexCall f ts xs) = IndexCall f (map (mapIndices rebaseIndex) ts) (map rebaseIndex xs)
            rebaseIndex (IndexSuccessor x) = IndexSuccessor (rebaseIndex x)
            rebaseIndex (IndexTyped ty x) = typedIndex (mapIndices rebaseIndex ty) (rebaseIndex x)
            rebaseIndex (IndexLambda slots ty x) = IndexLambda slots (mapIndices rebaseIndex ty) (rebaseIndex x)
            rebaseIndex (IndexApply f x) = IndexApply (rebaseIndex f) (rebaseIndex x)
            rebaseIndex x = x
        forM_ (zip prefixFields (take recordPrefix ins)) $ \(f,domain) ->
          save f [] (object ["name" .= f,"displayName" .= f,"kind" .= ("function" :: Text)
            ,"abstract" .= False,"parameters" .= (0 :: Int),"type" .= arrow [receiver] (mapIndices rebaseIndex domain)
            ,"projection" .= object ["proper" .= typeKey ty,"index" .= (1 :: Int)]])
        forM_ fields $ \f -> do
          fd <- definition inv f
          sig <- liftEither (signature inv fd)
          p <- liftEither (field inv "projection" fd)
          actualIns <- liftEither ((\xs -> captureTypes ++ xs) <$> traverse instantiate (inputs sig))
          actualOut <- liftEither (instantiate (output sig))
          unless (parameters sig == n && take prefix actualIns == captureTypes && length actualIns == recordPrefix+1
            && typeKey (last actualIns) == typeKey ty
            && get "proper" p == String s && get "index" p == toJSON (sourceParameters+1)) (abort Syntax "Dependent or malformed proper record projection")
          let nativeOut = if recordPrefix == 0 then actualOut else mapIndices rebaseIndex actualOut
              fd' = set "type" (arrow [if recordPrefix == 0 then Named s args else receiver] nativeOut) $ set "projection"
                (set "proper" (String (typeKey ty)) (set "index" (Number 1) p)) $ clone inv f args fd
          save f args fd'
      _ -> abort Representation "Record requires exactly one constructor"
    let d' = set "nativeContextIndices" (toJSON contexts) $ set "type" (telescope indexTypes (object ["term" .= object ["tag" .= ("sort" :: Text)]]))
          $ set "parameters" (Number 0) $ set "fields" (toJSON nativeFields)
          $ set "nativeRecordCaptures" (toJSON (if get "kind" d == String "record" then recordPrefix else 0))
          $ (case (get "kind" d,cs) of
              (String "record",[c]) -> set "constructor" (String (instanceKey c args))
              _ -> set "constructors" (toJSON (map (`instanceKey` args) cs))) $ clone inv s args d
    save s args d'

-- Finite nesting of a nonrecursive generic record is not polymorphic
-- recursion. Follow original payload carrier references, never instance names.
nonRecursiveTemplate :: Inventory -> Text -> Bool
nonRecursiveTemplate inv root = inspect (S.singleton root) root
  where
    inspect seen symbol = case M.lookup symbol (declarations inv) of
      Just d | get "kind" d `elem` [String "record",String "datatype"] ->
        let cs = if get "kind" d == String "record" then either (const []) ((:[]) . string) (field inv "constructor" d)
              else either (const []) (map string . array) (field inv "constructors" d)
        in all (\c -> case M.lookup c (declarations inv) >>= either (const Nothing) Just . signature inv of
          Just sig -> all (walk seen) (inputs sig)
          Nothing -> False) cs
      _ -> True
    walk seen (Named s xs) = all (walk seen) xs && s /= root && (S.member s seen || inspect (S.insert s seen) s)
    walk seen (FamilyApplication f xs) = all (walk seen) (f:xs)
    walk seen (Callable a b) = all (walk seen) (b:a)
    walk seen (SchemaValue ds _) = all (walk seen) ds
    walk seen (SelectedFamily value) = walk seen value
    walk seen (Runtime domain _) = walk seen domain
    walk _ _ = True
-- Signatures can be the only use of an index calculation. Clone its checked
-- body as well, preserving the call dependency for the native admission pass.
ensureIndex :: Inventory -> IndexExpr -> Build ()
ensureIndex inv (IndexCall f args values) = do
  mapM_ (ensureIndex inv) values
  ensureFunction inv [] f args
ensureIndex inv (IndexProject _ _ receiver) = ensureIndex inv receiver
ensureIndex inv (IndexSuccessor i) = ensureIndex inv i
ensureIndex inv (IndexTyped _ x) = ensureIndex inv x
ensureIndex inv (IndexLambda _ ty x) = ensureType inv [] ty >> ensureIndex inv x
ensureIndex inv (IndexApply f x) = ensureIndex inv f >> ensureIndex inv x
ensureIndex inv (IndexConstructor _ _ xs) = mapM_ (ensureIndex inv) xs
ensureIndex _ _ = pure ()

-- The compiled value environment is independent of type-codomain binding.
data Binding = Static Type | Dynamic Type deriving (Eq,Show)
isDynamic :: Binding -> Bool
isDynamic Dynamic{} = True
isDynamic _ = False

-- Root selection supplies static arguments only. Reconstruct the remaining
-- checked family telescope before reducing a module equation, so its runtime
-- indices retain their domains and order. The resulting canonical family is
-- materialized by the same path used for ordinary type references.
canonicalCarrierRoot :: Inventory -> Text -> [Type] -> Either Refusal Type
canonicalCarrierRoot inv s args = do
  d <- maybe (refuse Syntax "Missing module carrier") Right (M.lookup s (declarations inv))
  (kinds,indices,_) <- familySignature inv d
  validateArguments inv kinds args
  domains <- traverse (substitute args) indices
  let values = zipWith Runtime domains (map IndexInput [0..])
      context = reverse (map Just values)
      term = get "term" (sourceTypeTerm inv (length domains) (Named s (args ++ values)))
  readType inv context term

ensureCarrierRoot :: Inventory -> Text -> [Type] -> Build Text
ensureCarrierRoot inv s args = do
  carrier <- liftEither (canonicalCarrierRoot inv s args)
  case carrier of
    Named owner _ -> do
      d <- definition inv owner
      unless (get "kind" d `elem` map String ["record","datatype"])
        (abort Semantics "Module carrier equation does not resolve to an algebraic carrier")
    _ -> abort Semantics "Module carrier equation does not resolve to an algebraic carrier"
  ensureType inv [] carrier
  let key = typeKey carrier
  present <- gets (M.member key . ready)
  unless present (abort Representation "Canonical module carrier was not materialized")
  pure key

-- A module copy's parameter slots need not match its canonical constructor's
-- slots. Recover the latter from the checked result family, materialize that
-- family, and verify the whole instantiated telescope before redirecting a
-- public root. Keep the source alias in the inventory and root correspondence.
ensureConstructorRoot :: Inventory -> Text -> [Type] -> Build Text
ensureConstructorRoot inv s args = do
  d <- definition inv s
  sig <- liftEither (signature inv d)
  liftEither (validateArguments inv (parameterKinds sig) args)
  ins <- liftEither (traverse (substitute args) (inputs sig))
  out <- liftEither (substitute args (output sig))
  let term = object ["tag" .= ("constructor" :: Text),"symbol" .= s,"eliminations" .= ([] :: [Value])]
  canonical <- case Reduction.reduceHead inv term of
    Just (value,_) | get "tag" value == String "constructor",null (array (get "eliminations" value)) ->
      pure (string (get "symbol" value))
    _ -> abort Semantics "Module constructor lacks a checked canonical identity"
  actualArgs <- case out of
    Named _ ts -> pure (staticArguments ts)
    _ -> abort Representation "Module constructor result is not a named carrier"
  ensureType inv [] out
  let key = instanceKey canonical actualArgs
  target <- gets (M.lookup key . ready) >>= maybe
    (abort Representation "Canonical module constructor was not materialized") pure
  actualType <- liftEither (field inv "type" target)
  unless (get "kind" target == String "constructor"
    && Reduction.canonicalTerm actualType == Reduction.canonicalTerm (arrow ins out))
    (abort Semantics "Module constructor telescope differs from its canonical instance")
  pure key

-- Proper projection copies similarly name a checked original field. Their
-- eta-short forwarding body and complete receiver/result telescope must agree
-- with that field; a matching result type alone cannot identify a projection.
ensureProjectionRoot :: Inventory -> Text -> [Type] -> Build Text
ensureProjectionRoot inv s args = do
  d <- definition inv s
  sig <- liftEither (signature inv d)
  liftEither (validateArguments inv (parameterKinds sig) args)
  ins <- liftEither (traverse (substitute args) (inputs sig))
  out <- liftEither (substitute args (output sig))
  p <- liftEither (field inv "projection" d)
  tree <- liftEither (field inv "compiled" d)
  let canonical = string (get "original" p)
      forwarded = object ["tag" .= ("variable" :: Text),"index" .= (0 :: Int)
        ,"eliminations" .= [object ["tag" .= ("project" :: Text),"symbol" .= canonical]]]
      body = get "body" tree
      equation = case array (get "binders" tree) of
        [_] -> body
        [] | get "tag" body == String "lambda", get "binds" (get "abstraction" body) == Bool True ->
          get "body" (get "abstraction" body)
        _ -> Null
  unless (get "abstract" d == Bool False && not (T.null canonical)
    && get "tag" tree == String "done"
    && Reduction.canonicalTerm equation == Reduction.canonicalTerm forwarded)
    (abort Semantics "Module projection lacks a checked field-forwarding equation")
  (receiver,owner,ownerArgs) <- case ins of
    [ty@(Named owner actual)] -> pure (ty,owner,actual)
    _ -> abort Representation "Module projection needs a single record receiver"
  ownerDef <- definition inv owner
  fields <- map string . array <$> liftEither (field inv "fields" ownerDef)
  declaredOwner <- case get "proper" p of
    String sourceOwner -> liftEither (canonicalCarrierRoot inv sourceOwner args)
    _ -> abort Semantics "Module projection has no checked owner"
  unless (get "kind" ownerDef == String "record" && typeKey declaredOwner == typeKey receiver && canonical `elem` fields)
    (abort Semantics "Module projection does not name a field of its receiver")
  ensureType inv [] receiver
  let key = instanceKey canonical (staticArguments ownerArgs)
  target <- gets (M.lookup key . ready) >>= maybe
    (abort Representation "Canonical module projection was not materialized") pure
  actualType <- liftEither (field inv "type" target)
  unless (get "kind" target == String "function"
    && get "proper" (get "projection" target) == String (typeKey receiver)
    && Reduction.canonicalTerm actualType == Reduction.canonicalTerm (arrow ins out))
    (abort Semantics "Module projection telescope differs from its canonical instance")
  pure key

ensureFunction :: Inventory -> [Text] -> Text -> [Type] -> Build ()
ensureFunction inv stack s actualArgs = do
  let (args,captures) = captureArguments actualArgs
      prefix = length captures
      captureTypes = map (materializeCaptures . fst) captures
      schemaArgs = map materializeCaptures args
      instantiate sourceType = substitute schemaArgs (shiftIndices prefix sourceType)
  exists <- cached inv s args
  when (exists && s `elem` stack) $ do
    d <- definition inv s
    unless (terminationChecked inv d) (abort Semantics "Recursive specialization lacks checked safe-module termination")
  unless exists $ do
    when (s `elem` stack) (abort Semantics ("Recursive specialized helper: " <> s))
    d <- definition inv s
    sig <- liftEither (signature inv d)
    liftEither (validateArguments inv (parameterKinds sig) args)
    ins <- liftEither ((\xs -> captureTypes ++ xs) <$> traverse instantiate (inputs sig))
    out <- liftEither (instantiate (output sig))
    mapM_ (ensureType inv []) (out:ins)
    p <- liftEither (field inv "projection" d)
    case get "proper" p of
      String owner -> ensureType inv [] (Named owner args)
      _ -> do
        when (get "abstract" d == Bool True || get "opaque" d == Bool True) (abort Semantics "Opaque helper body cannot justify specialization")
        let header = set "type" (arrow ins out) $ set "compiled" Null $ clone inv s args d
        save s args header
        body <- (if get "kind" d == String "primitive" then pure Null else do
          tree <- liftEither (field inv "compiled" d)
          sourceEnv <- liftEither (sourceArguments (argumentSlots sig) (map Static schemaArgs) (map Dynamic (drop prefix ins)))
          let env = map Dynamic captureTypes ++ drop (dropped sig) sourceEnv
          specializeTree inv (s:stack) env out (prefixTree prefix tree)) `catchError` \reason -> do
            modify' $ \st -> st {ready = M.delete (instanceKey s args) (ready st), recorded = M.delete (instanceKey s args) (recorded st)}
            throwError (context ("Specializing " <> s <> ": ") reason)
        let d' = set "type" (arrow ins out) $ set "compiled" body $ set "projection"
              (if runtimeDropped sig > 0 then set "index" (toJSON (runtimeDropped sig + 1)) p else Null)
              $ clone inv s args d
        save s args d'

prefixTree :: Int -> Value -> Value
prefixTree 0 tree = tree
prefixTree count tree = case string (get "tag" tree) of
  "done" -> leaf
  "absurd" -> leaf
  "case" -> set "argument" (set "value" (case get "value" (get "argument" tree) of
      Number n -> Number (n + fromIntegral count); value -> value) (get "argument" tree))
    $ set "constructors" (toJSON [set "branch" (branch (get "branch" b)) b | b <- array (get "constructors" tree)])
    $ set "eta" (if get "eta" tree == Null then Null else set "branch" (branch (get "branch" (get "eta" tree))) (get "eta" tree))
    $ set "catchall" (if get "catchall" tree == Null then Null else prefixTree count (get "catchall" tree)) tree
  _ -> tree
  where
    leaf = set "binders" (toJSON (replicate count (object ["value" .= ("captured-index" :: Text),"info" .= info]) ++ array (get "binders" tree))) tree
    branch b = set "tree" (prefixTree count (get "tree" b)) b

runtimeBindings :: [Binding] -> [Maybe Type]
runtimeBindings env = [case binding of
    Static ty -> Just ty
    Dynamic ty -> Just (Runtime ty (IndexInput (length (filter isDynamic (drop (i+1) env)))))
  | (i,binding) <- zip [0..] env]

specializeTree :: Inventory -> [Text] -> [Binding] -> Type -> Value -> Build Value
specializeTree inv stack = specializeTreeIn inv stack []

specializeTreeIn :: Inventory -> [Text] -> [(Type,Type)] -> [Binding] -> Type -> Value -> Build Value
specializeTreeIn inv stack equations env out tree
  | get "tag" tree == String "case",get "copattern" tree /= Bool True
  ,Right i <- number (get "value" (get "argument" tree))
  ,Right (Dynamic stored) <- at i env
  ,Just (concrete,premises) <- resolveStoredFamily inv (reverse env) stored = do
      ensureType inv stack concrete
      rewritten <- specializeTreeIn inv stack equations (take i env ++ [Dynamic concrete] ++ drop (i+1) env) out tree
      pure (object ["tag" .= ("native-schema-case" :: Text)
        ,"$occurrence" .= get "$occurrence" tree
        ,"position" .= length (filter isDynamic (take i env))
        ,"memberType" .= asType (length (filter isDynamic env)) concrete
        ,"tree" .= rewritten,"reductionEvidence" .= object ["declarations" .= premises]])
  | otherwise = case string (get "tag" tree) of
  "absurd" -> do
    let bs = array (get "binders" tree)
    unless (length bs == length env) (abort Syntax "Absurd leaf binder count mismatch")
    pure $ set "binders" (toJSON [b | (b,e) <- zip bs env,isDynamic e]) tree
  "done" -> do
    let bs = array (get "binders" tree)
    unless (length bs <= length env) (abort Syntax "Specialized leaf binder count mismatch")
    let missing = length env - length bs
        supplied = [Reduction.variable i | i <- reverse [0..missing-1]]
    expandedBody <- maybe (abort Syntax "Unsupported eta expansion") pure
      (Reduction.applyTerms (Reduction.shift missing (get "body" tree)) supplied)
    (_,body) <- expression inv stack (reverse env) (Just out) expandedBody
    let allBinders = bs ++ replicate missing (object ["value" .= ("_" :: Text),"info" .= info])
    pure $ set "body" body $ set "binders" (toJSON [b | (b,e) <- zip allBinders env,isDynamic e]) tree
  "case" | get "copattern" tree == Bool True -> do
    i <- liftEither (number (get "value" (get "argument" tree)))
    unless (i == length env && get "catchall" tree == Null && get "eta" tree == Null
      && null (array (get "literals" tree))) (abort Syntax "Malformed record copattern split")
    (owner,args) <- case out of
      Named owner args -> pure (owner,staticArguments args)
      _ -> abort Representation "Copattern result requires a named record"
    record <- definition inv owner
    unless (get "kind" record == String "record") (abort Semantics "Copattern result is not a record")
    fields <- map string . array <$> liftEither (field inv "fields" record)
    let branches = array (get "constructors" tree)
    unless (length branches == length fields && all (\f -> length (filter ((== String f) . get "symbol") branches) == 1) fields)
      (abort Semantics "Copattern fields do not cover the result record")
    rewritten <- forM branches $ \branch -> do
      let f = string (get "symbol" branch); b = get "branch" branch
      unless (get "arity" b == Number 0) (abort Syntax "Projection pattern has constructor payloads")
      fd <- definition inv f
      sig <- liftEither (signature inv fd)
      result <- liftEither (substitute args (output sig))
      body <- specializeTreeIn inv stack equations env result (get "tree" b)
      pure $ set "symbol" (String (instanceKey f args)) $ set "branch" (set "tree" body b) branch
    pure $ set "argument" (set "value" (toJSON (length (filter isDynamic env))) (get "argument" tree))
      $ set "constructors" (toJSON rewritten) tree
  "case" -> do
    i <- liftEither (number (get "value" (get "argument" tree)))
    selected <- liftEither (at i env)
    ty <- case selected of Dynamic t -> pure t; _ -> abort Semantics "Case split on a type parameter"
    let owner = typeKey ty; args = case ty of Named _ as -> staticArguments as; _ -> []
    ensureType inv [] ty
    let branch c b = do
          cd <- gets (M.lookup (instanceKey c args) . ready) >>= maybe (abort Syntax "Case constructor does not belong to specialized carrier") pure
          unless (get "family" cd == String owner) (abort Syntax "Case constructor owner mismatch")
          original <- definition inv c
          sig <- liftEither (signature inv original)
          sourceParameters <- liftEither (field inv "parameters" original >>= number)
          let runtimeParameters = sourceParameters - parameters sig
              fieldSchemas = drop runtimeParameters (inputs sig)
              position = length (filter isDynamic (take i env))
              count = length fieldSchemas
              contextual = case ty of Named _ xs -> take runtimeParameters [ix | Runtime _ ix <- xs]; _ -> []
              record = case ty of
                Named sourceOwner _ -> get "kind" (M.findWithDefault Null sourceOwner (declarations inv)) == String "record"
                _ -> False
              payloadIndices = map IndexInput [position..position+count-1]
              replacement = IndexConstructor c args (if record then contextual ++ payloadIndices else payloadIndices)
              reindex = mapIndices rewrite
              rewrite (IndexInput j) | j == position = replacement
                                    | j > position = IndexInput (j+count-1)
              rewrite (IndexConstructor name ts xs) = IndexConstructor name (map reindex ts) (map rewrite xs)
              rewrite (IndexProject name ts x) = IndexProject name (map reindex ts) (rewrite x)
              rewrite (IndexCall name ts xs) = IndexCall name (map reindex ts) (map rewrite xs)
              rewrite (IndexSuccessor x) = IndexSuccessor (rewrite x)
              rewrite (IndexTyped ty x) = typedIndex (reindex ty) (rewrite x)
              rewrite (IndexLambda slots ty x) = IndexLambda slots (reindex ty) (rewrite x)
              rewrite (IndexApply f x) = IndexApply (rewrite f) (rewrite x)
              rewrite x = x
              bindings = map rewrite contextual ++ payloadIndices
              change (Dynamic domain) = Dynamic (reindex domain)
              change binding = binding
          fields <- liftEither (traverse (instantiate (map reindex args) (M.fromList (zip [0..] bindings))) fieldSchemas)
          arity <- liftEither (number (get "arity" b))
          unless (arity == length fields) (abort Syntax "Specialized case payload arity mismatch")
          let branchEnv = map change (take i env) ++ map Dynamic fields ++ map change (drop (i+1) env)
          constructorResult <- liftEither (instantiate (map reindex args) (M.fromList (zip [0..] bindings)) (output sig))
          let branchEquations = (constructorResult,reindex ty) : [(reindex a,reindex b) | (a,b) <- equations]
              (facts,premises) = branchIndexBindings inv (reverse branchEnv) position count branchEquations
              refine (Dynamic domain) = Dynamic (replaceKnownInputs facts domain)
              refine binding = binding
              -- Repeated implicit indices in a checked case telescope may
              -- name the same value. Transport those aliases in source terms
              -- as well as in their domains, retaining every runtime binder.
              sourcePositions = [length branchEnv-j-1 | (j,binding) <- zip [0..] branchEnv,isDynamic binding]
              sourceBindings = [case binding of
                  Dynamic _ | Just (IndexInput target) <- M.lookup (length (filter isDynamic (take j branchEnv))) facts
                    ,target >= 0,target < length sourcePositions -> Reduction.variable (sourcePositions !! target)
                  _ -> Reduction.variable (length branchEnv-j-1)
                | (j,binding) <- zip [0..] branchEnv]
              refinedEquations = [(replaceKnownInputs facts a,replaceKnownInputs facts b) | (a,b) <- branchEquations]
          child <- if sourceBindings == map Reduction.variable (reverse [0..length branchEnv-1])
            then pure (get "tree" b)
            else maybe (abort Syntax "Cannot transport checked branch index aliases") pure
              (Reduction.rewriteTree inv (length branchEnv) sourceBindings (get "tree" b))
          result <- specializeTreeIn inv stack refinedEquations (map refine branchEnv)
            (replaceKnownInputs facts (reindex out)) child
          let priorEvidence = case get "reductionEvidence" result of
                evidence@Object{} -> evidence
                _ -> object []
              allPremises = S.toAscList (S.fromList (premises ++ map string (array (get "declarations" priorEvidence))))
          pure (set "tree" (if null premises then result else set "reductionEvidence"
            (set "declarations" (toJSON allPremises) priorEvidence) result) b)
    cs <- forM (array (get "constructors" tree)) $ \b -> do
      let c = string (get "symbol" b)
      b' <- branch c (get "branch" b)
      pure (set "symbol" (String (instanceKey c args)) (set "branch" b' b))
    let eta = get "eta" tree
    eta' <- if eta == Null then pure Null else do
      let c = string (get "constructor" eta)
      b <- branch c (get "branch" eta)
      pure $ set "constructor" (String (instanceKey c args)) $ set "branch" b
        $ set "fields" (toJSON [instanceKey (string f) args | f <- array (get "fields" eta)]) eta
    catchall <- if get "catchall" tree == Null then pure Null
      else specializeTreeIn inv stack equations env out (get "catchall" tree)
    -- Literal and copattern modes remain visible to the native rule gate.
    pure $ set "argument" (set "value" (toJSON (length (filter isDynamic (take i env)))) (get "argument" tree))
      $ set "constructors" (toJSON cs) $ set "eta" eta' $ set "catchall" catchall tree
  _ -> abort Syntax "Specialization requires a supported finite compiled body"

unify :: M.Map Int Type -> Type -> Type -> Either Refusal (M.Map Int Type)
unify known (Callable as b) (Callable cs d) = do
  unless (length as == length cs) (refuse Semantics "Callback arity mismatch")
  foldM (\next (a,c) -> unify next a c) known (zip (as ++ [b]) (cs ++ [d]))
unify known (SchemaValue ds l) (SchemaValue es m) | length ds == length es = do
  levels <- constrainUniverse known l m
  foldM (\next (d,e) -> unify next d e) levels (zip ds es)
unify known (SelectedFamily value) (SelectedFamily actual) = unify known value actual
unify known Unused Unused = Right known
unify known (Level l) (Level actual) = constrainUniverse known l actual
-- This pass infers only static substitutions. Runtime equalities are retained
-- in serialized signatures and checked by AlgebraicTarget after specialization.
-- Varying runtime indices share a family instance; fixed fibres used as static
-- type arguments still retain their indices in the outer instance identity.
unify known (Runtime domain _) (Runtime actual _) = unify known domain actual
unify known (Parameter i) actual = case M.lookup i known of
  Nothing -> Right (M.insert i actual known)
  Just t | t == actual -> Right known
  Just t@FamilyExpression{} | FamilyExpression{} <- actual -> unify known t actual
  -- A static argument may itself contain runtime indices. Keep the chosen
  -- argument (and its capture layout); the target checks index equality in
  -- the actual branch context. Re-inferring it as a fixed fibre would create
  -- a different nominal carrier at each constructor branch.
  Just t@Named{} | Named{} <- actual -> unify known t actual
  _ -> refuse Semantics ("Inconsistent concrete type arguments: " <> T.pack (show (M.lookup i known,actual)))
unify known (Open i l) (Open j m) | i == j && l == m = Right known
-- A template family slot and the caller's symbolic family have separate
-- namespaces. Infer their domains and universe before binding the template
-- slot to the complete caller identity; repeated occurrences must still agree.
unify known (FamilyParameter i domains level) actual@(FamilyParameter _ actualDomains actualLevel) = do
  checked <- unify known (SchemaValue domains level) (SchemaValue actualDomains actualLevel)
  let args = [M.findWithDefault (Parameter slot) slot checked | slot <- [0..maximum (0:M.keys checked)]]
  resolved <- substitute args (SchemaValue domains level)
  -- Ordinary value inference leaves runtime equalities to the target. Family
  -- telescope indices bind their own domains and must agree here as well.
  unless (indexNormalForm resolved == indexNormalForm (SchemaValue actualDomains actualLevel))
    (refuse Semantics "Symbolic family has incompatible dependent domains or universe")
  unify checked (Parameter i) actual
unify known (FamilyParameter i _ _) actual@OpenFamily{} = unify known (Parameter i) actual
unify known (FamilyParameter i _ _) actual@FamilyExpression{} = unify known (Parameter i) actual
unify known (FamilyParameter i _ _) actual@SelectedFamily{} = unify known (Parameter i) actual
unify known a@(FamilyExpression domainA _ bodyA levelA) b@(FamilyExpression domainB _ bodyB levelB) = do
  domains <- unify known domainA domainB
  levels <- unify domains (Level levelA) (Level levelB)
  inferred <- unify levels bodyA bodyB
  let args = [M.findWithDefault (Parameter i) i inferred | i <- [0..maximum (0:M.keys inferred)]]
  resolved <- substitute args a
  unless (fst (captureArguments [resolved]) == fst (captureArguments [b]))
    (refuse Semantics "Type-family lambda bodies have different bound indices or carriers")
  pure inferred
unify known a@OpenFamily{} b@OpenFamily{} | a == b = Right known
unify known (FamilyApplication (FamilyParameter i _ _) indices) actual
  | Just expression@FamilyExpression{} <- M.lookup i known = do
      let args = [M.findWithDefault (Parameter slot) slot known | slot <- [0..maximum (i:M.keys known)]]
      values <- traverse (substitute args) indices
      applied <- applyTypeFamily expression values
      unify known applied actual
unify known (FamilyApplication f xs) (FamilyApplication g ys) | length xs == length ys = do
  first <- unify known f g
  foldM (\m (a,b) -> unify m a b) first (zip xs ys)
unify known (Named s xs) (Named t ys) | s == t && length xs == length ys =
  foldM (\m (a,b) -> unify m a b) known (zip xs ys)
unify _ expected actual = refuse Semantics ("Concrete carrier mismatch: expected " <> T.pack (show expected) <> "; actual " <> T.pack (show actual))

-- Reconstruct source identities for checked definitional comparison. This is
-- also used when specializing static closures; emitted calls keep their own
-- specialized identities.
sourceTypeTerm :: Inventory -> Int -> Type -> Value
sourceTypeTerm inv = sourceTypeAt
  where
    sourceTypeAt depth (Callable domains out) = arrows depth (map resolve domains) (resolve out)
      where
        resolve = applyCallback (map IndexInput [depth..depth+length domains-1])
        arrows n [] result = sourceTypeAt n result
        arrows n (domain:rest) result = object ["term" .= object ["tag" .= ("pi" :: Text)
          ,"domain" .= object ["info" .= info,"type" .= sourceTypeAt n domain]
          ,"codomain" .= object ["binds" .= True,"body" .= arrows (n+1) rest result]]]
    sourceTypeAt depth (SchemaValue ds l) = object ["term" .= object
      ["tag" .= ("native-schema-value" :: Text),"domains" .= map (get "term" . sourceTypeAt depth) ds,"universe" .= levelValue l]]
    sourceTypeAt depth (SelectedFamily (Runtime _ index)) = object ["term" .= sourceIndex depth index]
    sourceTypeAt depth (Named s args) = object ["term" .= object ["tag" .= ("definition" :: Text)
      ,"symbol" .= s,"eliminations" .= map (application . get "term" . sourceTypeAt depth) ordered]]
      where
        ordered = either (const args) id $ do
          d <- maybe (refuse Syntax "Missing source family") Right (M.lookup s (declarations inv))
          (kinds,_,_,slots) <- familyLayout inv d
          sourceArguments slots (take (length kinds) args) (drop (length kinds) args)
    sourceTypeAt _ (Open slot level) = object ["term" .= object ["tag" .= ("native-open-type" :: Text)
      ,"slot" .= slot,"universe" .= levelValue level]]
    sourceTypeAt depth (OpenFamily slot domains level) = object ["term" .= object ["tag" .= ("native-open-family" :: Text)
      ,"slot" .= slot,"domains" .= map (get "term" . sourceTypeAt depth) domains,"universe" .= levelValue level]]
    sourceTypeAt depth (FamilyApplication family values) = let t = get "term" (sourceTypeAt depth family) in
      object ["term" .= set "eliminations" (toJSON (array (get "eliminations" t)
        ++ map (application . get "term" . sourceTypeAt depth) values)) t]
    sourceTypeAt depth (FamilyExpression domain slot body _) = case applyTypeFamily
        (FamilyExpression domain slot body (levelConstant 0)) [Runtime domain (IndexInput depth)] of
      Right result -> object ["term" .= object ["tag" .= ("lambda" :: Text)
        ,"abstraction" .= object ["binds" .= True,"body" .= get "term" (sourceTypeAt (depth+1) result)]]]
      Left _ -> object ["term" .= Null]
    sourceTypeAt depth (Runtime _ index) = object ["term" .= sourceIndex depth index]
    sourceTypeAt _ (Level (LevelExpr n terms)) = object ["term" .= object ["tag" .= ("level" :: Text)
      ,"level" .= object ["constant" .= n,"maximum" .=
        [object ["offset" .= offset,"term" .= levelAtomTerm atom] | (atom,offset) <- M.toAscList terms]]]]
    sourceTypeAt depth t = asType depth t
    levelAtomTerm (BoundLevel i) = Reduction.variable i
    levelAtomTerm (RigidLevel i) = object ["tag" .= ("native-open-level" :: Text),"slot" .= i]
    sourceIndex depth (IndexConstructor c _ values) = object ["tag" .= ("constructor" :: Text)
      ,"symbol" .= c,"eliminations" .= map (application . sourceIndex depth) values]
    sourceIndex depth (IndexNatural value) = indexTerm depth (IndexNatural value)
    sourceIndex depth (IndexSuccessor value) = object ["tag" .= ("constructor" :: Text)
      ,"symbol" .= builtin inv "suc","eliminations" .= [application (sourceIndex depth value)]]
    sourceIndex depth (IndexCall f types values) = object ["tag" .= ("definition" :: Text),"symbol" .= f
      ,"eliminations" .= map application ordered]
      where
        ts = map (get "term" . sourceTypeAt depth) types
        vs = map (sourceIndex depth) values
        ordered = either (const (ts ++ vs)) id $ do
          d <- maybe (refuse Syntax "Missing source calculation") Right (M.lookup f (declarations inv))
          sig <- signature inv d
          sourceArguments (drop (dropped sig) (argumentSlots sig)) ts vs
    sourceIndex depth (IndexProject f _ receiver) = let t = sourceIndex depth receiver in
      set "eliminations" (toJSON (array (get "eliminations" t)
        ++ [object ["tag" .= ("project" :: Text),"symbol" .= f]])) t
    sourceIndex depth (IndexTyped _ x) = sourceIndex depth x
    sourceIndex depth (IndexLambda slots _ body) = foldr (\_ value -> object
      ["tag" .= ("lambda" :: Text),"abstraction" .= object ["binds" .= True,"body" .= value]])
      (sourceIndex (depth+length slots) (bindIndexLocals (zip slots (map IndexInput [depth..])) body)) slots
    sourceIndex depth (IndexApply f x) = let t = sourceIndex depth f in
      set "eliminations" (toJSON (array (get "eliminations" t) ++ [application (sourceIndex depth x)])) t
    sourceIndex depth index = indexTerm depth index

-- Static type arguments can contain computed fibres. Compare their checked
-- definitional forms without discarding indices or assuming helper injectivity.
-- A blocked reduction leaves the original expression intact.
unifyIn :: Inventory -> [Binding] -> M.Map Int Type -> Type -> Type -> Either Refusal (M.Map Int Type)
unifyIn inv bindings known expected actual = case unify known expected actual of
  Right result -> Right result
  Left original -> case unify (M.map normal known) (normal expected) (normal actual) of
    Right result -> Right (M.union known result)
    Left _ -> Left original
  where
    env = runtimeBindings (filter isDynamic bindings)
    depth = length (filter isDynamic bindings)
    normal (Named s xs) = Named s (map normal xs)
    normal (Callable a b) = Callable (map normal a) (normal b)
    normal (SchemaValue ds l) = SchemaValue (map normal ds) l
    normal (SelectedFamily value) = SelectedFamily (normal value)
    normal (FamilyApplication f xs) = FamilyApplication (normal f) (map normal xs)
    normal (OpenFamily i xs l) = OpenFamily i (map normal xs) l
    normal (Runtime domain ix) =
      let ty = Runtime (normal domain) ix
      in case Reduction.reduceHead inv (get "term" (sourceTypeTerm inv depth ty)) of
        Just (reduced,_) -> either (const ty) id (readIndex inv env (normal domain) reduced)
        Nothing -> ty
    normal t = t

-- Recover fresh constructor indices from a branch's checked result fibre.
-- Only constructor injectivity is used; opaque computations are never inverted.
-- Runtime fields remain present and the target still checks all branch equations.
branchIndexBindings :: Inventory -> [Binding] -> Int -> Int -> [(Type,Type)] -> (M.Map Int IndexExpr,[Text])
branchIndexBindings inv bindings start count equations =
  let results = map (uncurry types) equations
      (pairs,premises) = (concatMap fst results,concatMap snd results)
      grouped = M.fromListWith S.union [(i,S.singleton value) | (i,value) <- pairs]
  in (M.mapMaybe (\values -> case S.toList values of [value] -> Just value; _ -> Nothing) grouped,premises)
  where
    dynamic = filter isDynamic bindings
    depth = length dynamic
    context = runtimeBindings dynamic
    fresh i = i >= start && i < start+count
    external domain value = all (not . fresh . (depth-1-))
      (Reduction.freeVariables (get "term" (sourceTypeTerm inv depth (Runtime domain value))))
    types (Named a xs) (Named b ys) | a == b && length xs == length ys =
      let results = zipWith types xs ys in (concatMap fst results,concatMap snd results)
    types (Runtime domain patternIndex) value@(Runtime actualDomain actualIndex) =
      let (domainPairs,domainPremises) = types domain actualDomain
          (index,premises) = case Reduction.reduceHead inv (get "term" (sourceTypeTerm inv depth value)) of
            Just (term,ps) | Right (Runtime _ ix) <- readIndex inv context actualDomain term -> (ix,ps)
            _ -> (actualIndex,[])
      in (domainPairs ++ indices domain patternIndex index,domainPremises ++ premises)
    types _ _ = ([],[])
    indices domain (IndexInput i) value | fresh i && external domain value = [(i,value)]
    indices domain value (IndexInput i) | fresh i && external domain value = [(i,value)]
    indices domain (IndexConstructor c _ xs) (IndexConstructor d _ ys) | c == d && length xs == length ys =
      concat (zipWith (indices domain) xs ys)
    indices domain (IndexSuccessor x) (IndexSuccessor y) = indices domain x y
    indices _ _ _ = []

-- A membership wrapper may be opened only when checked source reduction
-- identifies its concrete family. Source spelling or payload shape is never
-- sufficient evidence for this representation conversion.
resolveStoredFamily :: Inventory -> [Binding] -> Type -> Maybe (Type,[Text])
resolveStoredFamily inv env family@(FamilyApplication SelectedFamily{} _) = do
  let dynamic = filter isDynamic env
      depth = length dynamic
      raw = runtimeBindings dynamic
      normal ty = case ty of
        Named s xs -> let (ys,ps) = many xs in (Named s ys,ps)
        Callable ds out -> let (ys,ps) = many (out:ds) in case ys of
          result:domains -> (Callable domains result,ps)
          [] -> (ty,[])
        SchemaValue ds l -> let (ys,ps) = many ds in (SchemaValue ys l,ps)
        SelectedFamily value -> let (v,ps) = normal value in (SelectedFamily v,ps)
        FamilyApplication f xs -> let (g,ps) = normal f; (ys,qs) = many xs in (FamilyApplication g ys,ps ++ qs)
        Runtime domain ix ->
          let (d,ps) = normal domain; value = Runtime d ix
          in case Reduction.reduceHead inv (get "term" (sourceTypeTerm inv depth value)) of
            Just (reduced,qs) | Right result <- readIndex inv raw d reduced -> (result,ps ++ qs)
            _ -> (value,ps)
        _ -> (ty,[])
      many xs = let values = map normal xs in (map fst values,concatMap snd values)
      normalized = [(normal ty) | Dynamic ty <- dynamic]
      context = runtimeBindings [Dynamic ty | (ty,_) <- normalized]
      original = get "term" (sourceTypeTerm inv depth family)
  (reduced,premises) <- Reduction.reduceHead inv original
  concrete@Named{} <- either (const Nothing) Just (readType inv context reduced)
  pure (concrete,premises ++ concatMap snd normalized)
resolveStoredFamily _ _ _ = Nothing

expression :: Inventory -> [Text] -> [Binding] -> Maybe Type -> Value -> Build (Type,Value)
expression inv _ env (Just ty@Callable{}) term
  | get "tag" term /= String "lambda"
  ,Right (Runtime _ ix@IndexLambda{}) <- readIndex inv (runtimeBindings env) ty term = do
      ensureIndex inv ix
      pure (ty,set "$occurrence" (get "$occurrence" term) (indexTerm (length (filter isDynamic env)) ix))
expression inv stack env (Just stored) term
  | get "tag" term == String "constructor"
  ,Just (concrete,premises) <- resolveStoredFamily inv env stored = do
      (_,value) <- expression inv stack env (Just concrete) term
      ensureType inv stack stored
      let depth = length (filter isDynamic env)
      pure (stored,object ["tag" .= ("native-schema-inject" :: Text),"memberType" .= asType depth concrete
        ,"$occurrence" .= get "$occurrence" term
        ,"schemaType" .= asType depth stored,"value" .= value
        ,"reductionEvidence" .= object ["declarations" .= premises]])
expression inv stack env expected term = do
  result <- infer `catchError` \failure ->
    higherOrder inv stack env term `catchError` \closureFailure -> case Reduction.reduceHead inv term of
      Nothing -> throwError (context (message closureFailure <> "; ") failure)
      Just (reduced,premises) -> do
        (ty,value) <- expression inv stack env expected reduced
        pure (ty,set "reductionEvidence" (object ["before" .= term,"after" .= reduced,"declarations" .= premises]) value)
  forM_ expected $ \ty -> liftEither (either (Left . context "Specialized expression carrier mismatch: ") Right (unifyIn inv env M.empty ty (fst result)))
  pure result
  where
    es = array (get "eliminations" term)
    infer = case string (get "tag" term) of
      "lambda" | Just ty@(Callable domains out) <- expected -> do
        let depth = length (filter isDynamic env)
            positions = map IndexInput [depth..depth+length domains-1]
            localDomains = map (applyCallback positions) domains
            resultType = applyCallback positions out
        (context,source) <- foldM (\(context,value) domain -> do
          unless (get "tag" value == String "lambda")
            (abort Representation "Native lambda requires its complete argument telescope")
          let abstraction = get "abstraction" value
          body <- case get "binds" abstraction of
            Bool True -> pure (get "body" abstraction)
            Bool False -> pure (Reduction.shift 1 (get "body" abstraction))
            _ -> abort Syntax "Native lambda lacks checked binder information"
          pure (Dynamic domain:context,body)) (env,term) localDomains
        (_,value) <- expression inv stack context (Just resultType) source
        pure (ty,object ["tag" .= ("native-lambda" :: Text)
          ,"$occurrence" .= get "$occurrence" term
          ,"inputs" .= [asType (depth+i) domain | (i,domain) <- zip [0..] localDomains]
          ,"result" .= asType (depth+length domains) resultType,"body" .= value])
      "variable" -> do
        i <- liftEither (number (get "index" term))
        b <- liftEither (at i env)
        case b of
          Static _ -> abort Semantics "Type parameter used as a runtime value"
          Dynamic ty -> eliminate ty (set "index" (toJSON (length (filter isDynamic (take i env)))) (set "eliminations" (toJSON ([] :: [Value])) term)) es
      "literal" | get "tag" (get "literal" term) == String "natural" -> do
        _ <- liftEither (natural (get "value" (get "literal" term)))
        unless (null es) (abort Syntax "Applied natural literal")
        pure (Named (builtin inv "nat") [],term)
      "constructor" | Just d <- M.lookup (string (get "symbol" term)) (declarations inv)
        ,get "moduleInstanceCopy" d == Bool True ->
          case Reduction.reduceHead inv term of
            Just (reduced,premises) -> do
              (ty,value) <- expression inv stack env expected reduced
              pure (ty,set "reductionEvidence" (object
                ["before" .= term,"after" .= reduced,"declarations" .= premises]) value)
            Nothing -> abort Representation "Module constructor copy lacks a checked canonical head"
      "constructor" -> do
        let s = string (get "symbol" term)
        d <- definition inv s
        sig <- liftEither (signature inv d)
        sourceParameters <- liftEither (field inv "parameters" d >>= number)
        let runtimeParameters = sourceParameters - parameters sig
            contextualIndices = case expected of
              Just (Named _ xs) -> [ix | Runtime _ ix <- xs]
              _ -> []
            valueSig = sig {inputs = drop runtimeParameters (inputs sig)}
        -- Constructor terms omit their family parameters. Expected result types
        -- recover phantom parameters too; otherwise infer from ordered payloads.
        known <- if length es == length (inputs valueSig) then
          maybe (pure M.empty) (liftEither . unifyIn inv env M.empty (output sig)) expected else pure M.empty
        (types,values,indices,rest) <- argumentsFor valueSig runtimeParameters (take runtimeParameters contextualIndices) known es
        let tyArgs = types
        schemaOut <- liftEither (instantiate tyArgs indices (output sig))
        out <- if runtimeParameters == 0 then pure schemaOut else case expected of
          Just actual | typeKey actual == typeKey schemaOut -> pure actual
          _ -> abort Representation "Value-parameter constructor needs its contextual family type"
        ensureType inv [] out
        let recordConstructor = maybe False ((== String "record") . get "kind")
              (M.lookup (string (get "family" d)) (declarations inv))
            captureValues = [indexTerm (length (filter isDynamic env)) ix | recordConstructor
              ,ix <- map snd (snd (captureArguments tyArgs)) ++ take runtimeParameters contextualIndices]
            resultTerm = set "symbol" (String (instanceKey s tyArgs)) $ set "eliminations" (toJSON (map application (captureValues ++ values))) term
        eliminate out resultTerm rest
      "definition" | Just schema@SchemaValue{} <- expected
        ,Just d <- M.lookup (string (get "symbol" term)) (declarations inv)
        ,get "kind" d == String "record" -> schemaConstruction inv stack env schema d term
      "definition" -> do
        let s = string (get "symbol" term)
        d <- definition inv s
        unless (get "kind" d `elem` [String "function",String "primitive"]) (abort Semantics "Runtime call is not a checked function")
        sig <- liftEither (either (Left . context ("Signature of " <> s <> ": ")) Right (signature inv d))
        let slots = drop (dropped sig) (argumentSlots sig)
            staticEs = [(i,e) | (TypePosition i,e) <- zip slots es]
            valueElims = [e | (ValuePosition _,e) <- zip slots es] ++ drop (length slots) es
        unless (length staticEs == length [() | TypePosition{} <- slots]) (abort Representation "Partially applied type parameters")
        actualTypes <- liftEither (sequence [if parameterKinds sig !! i == UnusedKind then app e >> pure Unused
          else app e >>= readType inv (runtimeBindings env)
          | (i,e) <- staticEs])
        let explicit = M.fromList (zip (map fst staticEs) actualTypes)
        known <- if length valueElims == length (inputs sig) then
          maybe (pure explicit) (liftEither . unifyIn inv env explicit (output sig)) expected else pure explicit
        let omitted = runtimeDropped sig
        (types,values,indices,rest) <- argumentsFor (sig {inputs = drop omitted (inputs sig)}) omitted [] known valueElims
        ensureFunction inv stack s types
        out <- liftEither (instantiate types indices (output sig))
        let resultTerm = set "symbol" (String (instanceKey s types)) $ set "eliminations" (toJSON (map application ([indexTerm (length (filter isDynamic env)) ix | (_,ix) <- snd (captureArguments types)] ++ values))) term
        eliminate out resultTerm rest
      _ -> abort Syntax "Term outside first-order specialization"
    argumentsFor sig offset prefix initial elims = do
      unless (length elims >= length (inputs sig)) (abort Representation "Partially applied specialized operation")
      initialKnown <- liftEither (completeKnown inv sig initial)
      (known,values,actuals,indices) <- foldM step (initialKnown,[],[],M.fromList (zip [0..] prefix))
        (zip (inputs sig) (take (length (inputs sig)) elims))
      finalKnown <- liftEither (completeKnown inv sig known)
      args <- forM [0..parameters sig-1] $ \i -> maybe (abort Representation "Cannot resolve omitted type parameter") pure (M.lookup i finalKnown)
      unless (all closed (fst (captureArguments args))) (abort Representation "Unresolved concrete type arguments")
      liftEither (validateArguments inv (parameterKinds sig) (fst (captureArguments args)))
      expectedInputs <- liftEither (traverse (substitute args) (inputs sig))
      unless (length actuals == length expectedInputs && all (either (const False) (const True) . uncurry (unifyIn inv env M.empty)) (zip expectedInputs actuals))
        (abort Semantics "Specialized argument constraints do not agree")
      pure (args,values,indices,drop (length (inputs sig)) elims)
      where
        step (known,values,actuals,indices) (patternType,e) = do
          value <- liftEither (app e)
          let fill t = case instantiate [M.findWithDefault (Parameter i) i known | i <- [0..parameters sig-1]] indices t of
                Right actual | resolved actual -> Just actual
                _ -> Nothing
              resolved Parameter{} = False
              resolved FamilyParameter{} = False
              resolved (Named _ ts) = all resolved ts
              resolved (Callable a b) = all resolved (b:a)
              resolved (SchemaValue ds l) = all resolved ds && closed (Level l)
              resolved (SelectedFamily value) = resolved value
              resolved (FamilyApplication f xs) = all resolved (f:xs)
              resolved (FamilyExpression domain _ body level) = resolved domain && resolved body && closed (Level level)
              resolved (OpenFamily _ xs _) = all resolved xs
              resolved (Runtime domain index) = resolved domain && resolvedIndex index
              resolved t = closed t
              resolvedIndex (IndexConstructor _ ts xs) = all resolved ts && all resolvedIndex xs
              resolvedIndex (IndexProject _ ts x) = all resolved ts && resolvedIndex x
              resolvedIndex (IndexCall _ ts xs) = all resolved ts && all resolvedIndex xs
              resolvedIndex (IndexSuccessor x) = resolvedIndex x
              resolvedIndex (IndexTyped ty x) = resolved ty && resolvedIndex x
              resolvedIndex (IndexLambda _ ty x) = resolved ty && resolvedIndex x
              resolvedIndex (IndexApply f x) = resolvedIndex f && resolvedIndex x
              resolvedIndex _ = True
          (actual,v) <- expression inv stack env (fill patternType) value
          known' <- liftEither (unifyIn inv env known patternType actual)
          completed <- liftEither (completeKnown inv sig known')
          let concrete = instantiate [M.findWithDefault (Parameter i) i completed | i <- [0..parameters sig-1]] indices patternType
              -- The actual domain has already passed checked comparison.
              -- Reading against the unreduced declaration can lose an index
              -- whose domain is definitionally equal through a projection.
              index = concrete >>= \_ -> readIndex inv (runtimeBindings env) actual value
              recovered = recoverInputs indices patternType actual
              next = case index of
                Right (Runtime _ ix) -> M.insert (offset+length actuals) ix recovered
                _ -> recovered
          pure (completed,values ++ [v],actuals ++ [actual],next)
        recoverInputs table (Runtime _ (IndexInput i)) (Runtime _ ix) = M.insertWith (\_ prior -> prior) i ix table
        recoverInputs table (Named s xs) (Named t ys) | s == t && length xs == length ys =
          foldl (\known (a,b) -> recoverInputs known a b) table (zip xs ys)
        recoverInputs table (FamilyApplication f xs) (FamilyApplication g ys) | f == g && length xs == length ys =
          foldl (\known (a,b) -> recoverInputs known a b) table (zip xs ys)
        recoverInputs table _ _ = table
    eliminate ty value [] = pure (ty,value)
    eliminate (Callable domains out) value es@(_:_) = do
      unless (length es >= length domains) (abort Representation "Partial callback application requires runtime closure construction")
      (indices,actuals) <- foldM (\(prior,values) (patternType,e) -> do
        let domain = applyCallback prior patternType
        when (S.member (-1) (familyLocals domain)) (abort Representation "Dependent callback requires a representable argument index")
        argument <- liftEither (app e)
        (_,actual) <- expression inv stack env (Just domain) argument
        let index = case readIndex inv (runtimeBindings env) domain argument of
              Right (Runtime _ ix) -> ix
              _ -> IndexArgument (length prior)
        pure (prior ++ [index],values ++ [application actual])) ([],[]) (zip domains es)
      let result = applyCallback indices out
      when (S.member (-1) (familyLocals result)) (abort Representation "Dependent callback requires a representable argument index")
      let applied = set "eliminations" (toJSON (array (get "eliminations" value) ++ actuals)) value
      eliminate result applied (drop (length domains) es)
    eliminate ty@(Named owner args) value (e:rest) = do
      unless (get "tag" e == String "project") (abort Representation "Extra value application is unsupported")
      let f = string (get "symbol" e)
      fd <- definition inv f
      p <- liftEither (field inv "projection" fd)
      unless (get "proper" p == String owner) (abort Semantics "Projection applied to wrong specialized owner")
      ensureType inv [] ty
      sig <- liftEither (signature inv fd)
      out <- liftEither (substitute (staticArguments args) (output sig))
      let prior = array (get "eliminations" value)
          value' = set "eliminations" (toJSON (prior ++ [set "symbol" (String (instanceKey f (staticArguments args))) e])) value
      eliminate out value' rest
    eliminate _ _ _ = abort Representation "Projection from unresolved type"

-- Reify a named, nonrecursive record family as a collection of complete rows.
-- The target checks that every free payload domain has a native extent; this
-- stage retains the checked telescope and never invents a finite bound.
schemaConstruction :: Inventory -> [Text] -> [Binding] -> Type -> Value -> Value -> Build (Type,Value)
schemaConstruction inv stack env schema@(SchemaValue domains level) declaration source = do
  let symbol = string (get "name" declaration)
      depth = length (filter isDynamic env)
      es = array (get "eliminations" source)
  unless (nonRecursiveTemplate inv symbol) (abort Representation "Computed schema requires a nonrecursive record family")
  (kinds,indices,universe,slots) <- liftEither (familyLayout inv declaration)
  unless (length es >= length kinds && length es <= length kinds + length indices)
    (abort Representation "Computed schema has an incomplete static or excess runtime telescope")
  let staticEs = [e | (TypePosition _,e) <- zip slots es]
      valueEs = [e | (ValuePosition _,e) <- zip slots es]
  unless (length staticEs == length kinds) (abort Representation "Computed schema has incomplete static arguments")
  types <- liftEither (readStaticArguments inv (runtimeBindings env) kinds staticEs)
  values <- foldM (\prior (domain,e) -> do
    contextual <- liftEither (instantiate types (M.fromList (zip [0..] [ix | Runtime _ ix <- prior])) domain)
    value <- liftEither (app e >>= readIndex inv (runtimeBindings env) contextual)
    pure (prior ++ [value])) [] (zip indices valueEs)
  let remaining = drop (length values) indices
      variables = [Runtime domain (IndexInput (depth+i)) | (i,domain) <- zip [0..] domains]
      allValues = values ++ variables
  actualDomains <- liftEither (traverse (instantiate types (M.fromList (zip [0..] [ix | Runtime _ ix <- allValues]))) remaining)
  actualLevel <- liftEither (substituteLevel types universe)
  unless (actualDomains == domains && actualLevel == level)
    (abort Semantics "Computed schema does not match its stored family telescope")
  let member = Named symbol (types ++ allValues)
  ensureType inv stack schema
  ensureType inv stack member
  pure (schema,object ["tag" .= ("native-schema-build" :: Text)
    ,"$occurrence" .= get "$occurrence" source
    ,"schemaType" .= asType depth schema
    ,"domains" .= [asType (depth+i) domain | (i,domain) <- zip [0..] domains]
    ,"memberType" .= asType (depth+length domains) member
    ,"sourceFamily" .= symbol])
schemaConstruction _ _ _ _ _ _ = abort Semantics "Computed schema lacks a stored family type"

-- Monomorphize a checked helper at concrete function arguments. Closures are
-- compile-time terms; each free runtime value becomes an explicit input to the
-- generated first-order calculation. Its identity excludes captured values.
higherOrder :: Inventory -> [Text] -> [Binding] -> Value -> Build (Type,Value)
higherOrder inv stack env term = do
  unless (get "tag" term == String "definition") (abort Representation "No higher-order call")
  let source = string (get "symbol" term)
  d <- definition inv source
  unless (terminationChecked inv d && get "opaque" d == Bool False && get "abstract" d == Bool False)
    (abort Semantics "Closure specialization requires checked transparent termination")
  projection <- liftEither (field inv "projection" d)
  unless (projection == Null) (abort Representation "Higher-order projection requires argument recovery")
  rawType <- liftEither (field inv "type" d)
  args <- liftEither (traverse app (array (get "eliminations" term)))
  (slots,out) <- telescopeSlots rawType args
  let closures = [v | (slot,v) <- slots, case slot of ValueSlot{} -> False; StaticSlot -> False; _ -> True]
  unless (not (null closures)) (abort Representation "No concrete function or aggregate argument")
  let free = S.toAscList (S.fromList (concatMap Reduction.freeVariables closures))
  staticTypes <- liftEither (traverse (readType inv (runtimeBindings env))
    [v | (StaticSlot,v) <- slots])
  let lexicalTypes = [t | i <- free,Right (Static t) <- [at i env]]
  captures <- fmap concat $ forM free $ \i -> do
    binding <- liftEither (at i env)
    pure $ case binding of Dynamic t -> [(i,t)]; Static _ -> []
  let captureTypes = map snd captures
      runtimeTypes = [t | (ValueSlot t,_) <- slots]
      equations = concat [eqs | (AggregateSlot eqs,_) <- slots]
      refineIndex index = foldl (\current (_,left,right) -> if current == left then right else current) index equations
      refine = mapIndices (refineIndex . descend)
      descend (IndexConstructor c ts xs) = IndexConstructor c (map refine ts) (map (refineIndex . descend) xs)
      descend (IndexSuccessor x) = IndexSuccessor (refineIndex (descend x))
      descend (IndexCall f ts xs) = IndexCall f (map refine ts) (map (refineIndex . descend) xs)
      descend (IndexProject f ts x) = IndexProject f (map refine ts) (refineIndex (descend x))
      descend (IndexTyped ty x) = typedIndex (refine ty) (refineIndex (descend x))
      descend (IndexLambda slots ty x) = IndexLambda slots (refine ty) (refineIndex (descend x))
      descend (IndexApply f x) = IndexApply (refineIndex (descend f)) (refineIndex (descend x))
      descend x = x
      callerPosition i = length (filter isDynamic (drop (i+1) env))
      capturePositions = M.fromList [(callerPosition i,j) | (j,(i,_)) <- zip [0..] captures]
      valuePositions = M.fromListWith min [(callerPosition i,length captures+j)
        | (j,(_,v)) <- zip [0..] [(t,v) | (ValueSlot t,v) <- slots]
        ,get "tag" v == String "variable",null (array (get "eliminations" v))
        ,Right i <- [number (get "index" v)]]
      positions = M.union capturePositions valuePositions
      rebase = mapIndices rename
      rename (IndexInput i) = maybe (IndexCaptured (-1)) IndexInput (M.lookup i positions)
      rename (IndexConstructor c ts xs) = IndexConstructor c (map rebase ts) (map rename xs)
      rename (IndexSuccessor x) = IndexSuccessor (rename x)
      rename (IndexCall f ts xs) = IndexCall f (map rebase ts) (map rename xs)
      rename (IndexProject f ts x) = IndexProject f (map rebase ts) (rename x)
      rename (IndexTyped ty x) = typedIndex (rebase ty) (rename x)
      rename (IndexLambda slots ty x) = IndexLambda slots (rebase ty) (rename x)
      rename (IndexApply f x) = IndexApply (rename f) (rename x)
      rename x = x
      allTypes = map (rebase . refine) (captureTypes ++ runtimeTypes)
      resultType = rebase (refine out)
      n = length allTypes
      replacements depth = [case b of
          Static t -> get "term" (sourceType t)
          Dynamic _ -> case lookup i (zip (map fst captures) [0..]) of
            Just j -> Reduction.variable (depth-1-j)
            Nothing -> Null
        | (i,b) <- zip [0..] env]
      move depth v = maybe (abort Syntax "Closure substitution failed") pure (Reduction.substituteTerms (replacements depth) v)
  unless (and [independentAt i t | (i,t) <- zip [0..] allTypes] && independentAt n resultType)
    (abort Representation "Callback signature index must refer to an earlier explicit input")
  canonical <- forM slots $ \(slot,v) -> case slot of
    ValueSlot t -> pure (object ["input" .= typeValue (rebase (refine t))])
    _ -> Reduction.canonicalTerm <$> move (length captures) v
  let equationKey = [[typeValue (rebase (Runtime domain left)),typeValue (rebase (Runtime domain right))]
        | (domain,left,right) <- equations]
      key = source <> "@closure-" <> digest (BL.toStrict (encode (map typeValue (take (length captures) allTypes),canonical,equationKey)))
      shown = string (get "displayName" d) <> "<closure " <> T.takeEnd 12 key <> ">"
      variableAt i = Reduction.variable (n-1-i)
  unless (length stack < 128) (abort Representation "Static callback specialization depth exhausted")
  sourceEnv <- snd <$> foldM (\(position,values) (slot,v) -> case slot of
    ValueSlot _ -> pure (position+1,values ++ [variableAt position])
    _ -> do value <- move n v; pure (position,values ++ [value])) (length captures,[]) slots
  tree <- liftEither (field inv "compiled" d)
  body <- maybe (abort Representation "Cannot replay higher-order case bindings") pure (Reduction.rewriteTree inv n sourceEnv tree)
  nativeEquations <- forM equations $ \(domain,left,right) -> do
    let ty = rebase domain
        rebased index = case rebase (Runtime domain index) of Runtime _ result -> result; _ -> index
        l = rebased left; r = rebased right
    ensureType inv [] ty
    ensureIndex inv l
    ensureIndex inv r
    unless (independentAt n (Runtime ty l) && independentAt n (Runtime ty r))
      (abort Representation "Static container index equality has an unbound input")
    pure (object ["domain" .= asType n ty,"left" .= indexTerm n l,"right" .= indexTerm n r])
  let generated = set "name" (String key) $ set "displayName" (String shown)
        $ set "type" (sourceArrow allTypes resultType) $ set "compiled" body
        $ set "higherOrderOrigin" (String source)
        $ set "closureIndexEquations" (toJSON nativeEquations)
        $ set "closureSpecialization" (object ["origin" .= source,"arguments" .= canonical
            ,"captures" .= map typeValue (take (length captures) allTypes)
            -- Open extents used only inside a specialized body are still
            -- inputs of its native calculation (e.g. schema construction).
            ,"types" .= map bindingTypeValue (resultType:allTypes ++ staticTypes ++ lexicalTypes)]) d
      extended = inv {declarations = M.insert key generated (declarations inv)}
  ensureFunction extended stack key []
  modify' $ \st -> st {recorded = M.insert key (Instance source [] key) (recorded st)}
  captureValues <- forM captures $ \(i,t) -> snd <$> expression inv stack env (Just t) (Reduction.variable i)
  values <- forM [(t,v) | (ValueSlot t,v) <- slots] $ \(t,v) -> snd <$> expression inv stack env (Just t) v
  pure (out,object ["tag" .= ("definition" :: Text),"symbol" .= key,"eliminations" .= map application (captureValues ++ values)])
  where
    sourceType = sourceTypeAt 0
    sourceTypeAt = sourceTypeTerm inv
    sourceArrow = go 0
      where
        go depth [] out = sourceTypeAt depth out
        go depth (t:ts) out = object ["term" .= object ["tag" .= ("pi" :: Text)
          ,"domain" .= object ["type" .= sourceTypeAt depth t,"info" .= info]
          ,"codomain" .= object ["binds" .= True,"body" .= go (depth+1) ts out]]]
    independentAt bound = go S.empty
      where
        go locals (Named _ xs) = all (go locals) xs
        go locals (Callable a b) = all (go locals) (b:a)
        go locals (SchemaValue ds l) = all (go locals) ds && closed (Level l)
        go locals (SelectedFamily value) = go locals value
        go _ Open{} = True
        go _ family@OpenFamily{} = closed family
        go locals (FamilyExpression domain slot body level) = go locals domain && go (S.insert slot locals) body && closed (Level level)
        go locals (FamilyApplication f xs) = all (go locals) (f:xs)
        go locals (Runtime domain index) = go locals domain && check locals index
        go _ levelType@Level{} = closed levelType
        go _ _ = False
        check locals (IndexLocal slot) = S.member slot locals
        check _ (IndexInput i) = i >= 0 && i < bound
        check _ IndexCaptured{} = False
        check _ IndexArgument{} = True
        check _ IndexFamilyArgument{} = True
        check locals (IndexTyped ty x) = go locals ty && check locals x
        check locals (IndexLambda slots ty x) = go locals ty && check (locals `S.union` S.fromList slots) x
        check locals (IndexApply f x) = check locals f && check locals x
        check locals (IndexConstructor _ types values) = all (go locals) types && all (check locals) values
        check locals (IndexSuccessor value) = check locals value
        check locals (IndexCall _ types values) = all (go locals) types && all (check locals) values
        check locals (IndexProject _ types receiver) = all (go locals) types && check locals receiver
        check _ IndexNatural{} = True
    telescopeSlots ty [] = do
      out <- liftEither (readType inv (runtimeBindings env) (get "term" ty))
      pure ([],out)
    telescopeSlots ty (value:rest) = do
      let arrowTerm = get "term" ty
          rawDomain = get "type" (get "domain" arrowTerm)
          dom = case Reduction.reduceHead inv (get "term" rawDomain) of
            Just (reduced,_) -> set "term" reduced rawDomain
            Nothing -> rawDomain
          cod = get "codomain" arrowTerm
      unless (get "tag" arrowTerm == String "pi") (abort Representation "Overapplied higher-order helper")
      (slot,argument) <- if isUniverse dom || isLevelType inv dom then pure (StaticSlot,value)
        else if get "tag" (get "term" dom) == String "pi" then pure (ClosureSlot,value)
        else do
          ty <- liftEither (readType inv (runtimeBindings env) (get "term" dom))
          -- A checked aggregate that has no native first-order carrier may
          -- still be a compile-time argument. Retain all of its free runtime
          -- values as captures; never admit an unknown runtime aggregate.
          before <- gets id
          admitted <- (ensureType inv [] ty >> pure True) `catchError` \_ -> pure False
          modify' (const before)
          let concrete = maybe value fst (Reduction.reduceHead inv value)
              knownConstructor = get "tag" concrete == String "constructor" && case ty of
                Named owner _ -> maybe False ((== String owner) . get "family")
                  (M.lookup (string (get "symbol" concrete)) (declarations inv))
                _ -> False
          if admitted && not knownConstructor then pure (ValueSlot ty,value) else do
            unless (get "tag" concrete == String "constructor")
              (abort Representation "Higher-order aggregate must have a statically known constructor")
            cd <- definition inv (string (get "symbol" concrete))
            unless (case ty of Named owner _ -> get "family" cd == String owner; _ -> False)
              (abort Semantics "Static aggregate constructor has the wrong carrier")
            actual <- constructorResult ty cd concrete
            eqs <- case (ty,actual) of
              (Named owner expectedArgs,Named actualOwner actualArgs) | owner == actualOwner && length expectedArgs == length actualArgs ->
                fmap concat $ forM (zip expectedArgs actualArgs) $ \(expectedArg,actualArg) -> case (expectedArg,actualArg) of
                  (Runtime domain left,Runtime actualDomain right) | domain == actualDomain ->
                    pure [(domain,left,right) | left /= right]
                  _ | expectedArg == actualArg -> pure []
                  _ -> abort Semantics "Static aggregate parameters do not match its declared carrier"
              _ -> abort Semantics "Static aggregate result does not match its declared carrier"
            pure (AggregateSlot eqs,concrete)
      body <- if get "binds" cod == Bool False then pure (get "body" cod)
        else maybe (abort Syntax "Higher-order telescope substitution failed") pure (Reduction.substituteTerms [value] (get "body" cod))
      (slots,out) <- telescopeSlots body rest
      pure ((slot,argument):slots,out)
    constructorResult (Named _ expectedArgs) cd concrete = do
      count <- liftEither (field inv "parameters" cd >>= number)
      ctorType <- liftEither (field inv "type" cd)
      let supplied = take count expectedArgs
      unless (length supplied == count) (abort Syntax "Static aggregate parameter arity mismatch")
      payloads <- liftEither (traverse app (array (get "eliminations" concrete)))
      result <- foldM consume ctorType (map (get "term" . sourceTypeAt (length (filter isDynamic env))) supplied ++ payloads)
      unless (get "tag" (get "term" result) /= String "pi") (abort Syntax "Static aggregate payload arity mismatch")
      liftEither (readType inv (runtimeBindings env) (get "term" result))
      where
        consume ty value = do
          let t = get "term" ty; cod = get "codomain" t
          unless (get "tag" t == String "pi") (abort Syntax "Overapplied static aggregate constructor")
          if get "binds" cod == Bool False then pure (get "body" cod)
          else maybe (abort Syntax "Static aggregate constructor substitution failed") pure
            (Reduction.substituteTerms [value] (get "body" cod))
    constructorResult _ _ _ = abort Representation "Static aggregate carrier must be named"

data CallSlot = StaticSlot | ClosureSlot | AggregateSlot [(Type,IndexExpr,IndexExpr)] | ValueSlot Type
