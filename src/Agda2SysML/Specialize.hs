{-# LANGUAGE OverloadedStrings #-}
-- | Concrete specialization of checked first-order type templates. The source
-- inventory is retained; generated identities carry explicit origin/arguments.
module Agda2SysML.Specialize
  ( Result(..), Instance(..), Type(..), prepare, typeKey, typeValue, signature
  , Signature(..), IndexExpr(..), LevelExpr(..), ParameterKind(..), substitute, readType, constrainLevel, levelSymbols, typeAlias, nativeParameters, nativeFamilies ) where

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

data LevelExpr = LevelExpr Integer (M.Map Int Integer) deriving (Eq,Ord,Show)
data Type = Unused | Parameter Int | Open Int Integer | Named Text [Type] | Level LevelExpr
  | FamilyParameter Int [Type] LevelExpr | OpenFamily Int [Type] Integer | FamilyApplication Type [Type]
  | FamilyExpression Type Int Type LevelExpr
  | Runtime Type IndexExpr deriving (Eq,Ord,Show)
-- Runtime positions are absolute within a value telescope. Static arguments
-- on proper projections are retained until those declarations are cloned.
data IndexExpr = IndexInput Int | IndexCaptured Int | IndexLocal Int | IndexConstructor Text [Type] [IndexExpr]
  | IndexNatural Integer | IndexSuccessor IndexExpr
  | IndexProject Text [Type] IndexExpr | IndexCall Text [Type] [IndexExpr] deriving (Eq,Ord,Show)

-- A carrier/helper identity abstracts runtime values in its static arguments.
-- The captured values become an explicit, ordered telescope prefix; repeated
-- references share one slot. Closed fibres retain their concrete identity.
mapIndices :: (IndexExpr -> IndexExpr) -> Type -> Type
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
    free bound (FamilyApplication f xs) = S.unions (map (free bound) (f:xs))
    free bound (OpenFamily _ xs _) = S.unions (map (free bound) xs)
    free bound (Runtime domain index) = free bound domain `S.union` indices bound index
    free _ _ = S.empty
    indices bound (IndexLocal i) = if S.member i bound then S.empty else S.singleton i
    indices bound (IndexConstructor _ ts xs) = S.unions (map (free bound) ts ++ map (indices bound) xs)
    indices bound (IndexProject _ ts x) = S.unions (indices bound x:map (free bound) ts)
    indices bound (IndexCall _ ts xs) = S.unions (map (free bound) ts ++ map (indices bound) xs)
    indices bound (IndexSuccessor x) = indices bound x
    indices _ _ = S.empty

canonicalFamilies :: Type -> Type
canonicalFamilies ty = go M.empty start ty
  where
    start = maybe 0 (+1) (S.lookupMax (familyLocals ty))
    go names next (FamilyExpression domain slot body level) = FamilyExpression (go names next domain) next
      (go (M.insert slot next names) (next+1) body) level
    go names next (Named s xs) = Named s (map (go names next) xs)
    go names next (FamilyApplication f xs) = FamilyApplication (go names next f) (map (go names next) xs)
    go names next (OpenFamily i xs l) = OpenFamily i (map (go names next) xs) l
    go names next (Runtime domain index) = Runtime (go names next domain) (ix names next index)
    go _ _ t = t
    ix names _ (IndexLocal i) = IndexLocal (M.findWithDefault i i names)
    ix names next (IndexConstructor c ts xs) = IndexConstructor c (map (go names next) ts) (map (ix names next) xs)
    ix names next (IndexProject f ts x) = IndexProject f (map (go names next) ts) (ix names next x)
    ix names next (IndexCall f ts xs) = IndexCall f (map (go names next) ts) (map (ix names next) xs)
    ix names next (IndexSuccessor x) = IndexSuccessor (ix names next x)
    ix _ _ x = x

applyTypeFamily :: Type -> [Type] -> Either Refusal Type
applyTypeFamily (FamilyExpression domain slot body _) [Runtime actual value] | domain == actual =
  Right (canonicalFamilies (mapIndices replace body))
  where
    replace (IndexLocal i) | i == slot = value
    replace (IndexConstructor c ts xs) = IndexConstructor c (map (mapIndices replace) ts) (map replace xs)
    replace (IndexProject f ts x) = IndexProject f (map (mapIndices replace) ts) (replace x)
    replace (IndexCall f ts xs) = IndexCall f (map (mapIndices replace) ts) (map replace xs)
    replace (IndexSuccessor x) = IndexSuccessor (replace x)
    replace x = x
applyTypeFamily FamilyExpression{} _ = refuse Semantics "Type-family lambda has incompatible index arguments"
applyTypeFamily family xs = Right (FamilyApplication family xs)

captureArguments :: [Type] -> ([Type],[(Type,IndexExpr)])
captureArguments args = let (result,slots) = runState (traverse (visit S.empty . canonicalFamilies) args) [] in (result,slots)
  where
    visit locals (Named symbol xs) = Named symbol <$> traverse (visit locals) xs
    visit locals (FamilyApplication ty xs) = FamilyApplication <$> visit locals ty <*> traverse (visit locals) xs
    visit locals (FamilyExpression domain slot body level) = FamilyExpression <$> visit locals domain <*> pure slot
      <*> visit (S.insert slot locals) body <*> pure level
    visit locals (Runtime ty ix) = do
      domain <- visit locals ty
      let erase (IndexLocal slot) | S.member slot locals = IndexCaptured 0
          erase (IndexConstructor c ts xs) = IndexConstructor c ts (map erase xs)
          erase (IndexSuccessor x) = IndexSuccessor (erase x)
          erase (IndexProject f ts x) = IndexProject f ts (erase x)
          erase (IndexCall f ts xs) = IndexCall f ts (map erase xs)
          erase x = x
      if closed (Runtime domain (erase ix)) || not (S.null (familyLocals (Runtime domain ix)))
        then pure (Runtime domain ix) else do
        slots <- gets id
        let value = (domain,ix)
            slot = length (takeWhile (/= value) slots)
        when (slot == length slots) (modify' (++ [value]))
        pure (Runtime domain (IndexCaptured slot))
    visit _ ty = pure ty

shiftIndices :: Int -> Type -> Type
shiftIndices offset = mapIndices go
  where
    go (IndexInput i) = IndexInput (i+offset)
    go (IndexSuccessor i) = IndexSuccessor (go i)
    go (IndexConstructor c ts xs) = IndexConstructor c (map (shiftIndices offset) ts) (map go xs)
    go (IndexProject f ts i) = IndexProject f (map (shiftIndices offset) ts) (go i)
    go (IndexCall f ts xs) = IndexCall f (map (shiftIndices offset) ts) (map go xs)
    go ix = ix

materializeCaptures :: Type -> Type
materializeCaptures = mapIndices go
  where
    go (IndexCaptured slot) = IndexInput slot
    go (IndexSuccessor i) = IndexSuccessor (go i)
    go (IndexConstructor c ts xs) = IndexConstructor c (map materializeCaptures ts) (map go xs)
    go ix = ix

staticArguments :: [Type] -> [Type]
staticArguments = takeWhile (\x -> case x of Runtime{} -> False; _ -> True)
data ParameterKind = UnusedKind | LevelKind | TypeKind LevelExpr | FamilyKind [Type] LevelExpr deriving (Eq,Show)
data Signature = Signature { parameters :: Int, inputs :: [Type], output :: Type, dropped :: Int
  , parameterKinds :: [ParameterKind] }
  deriving (Eq,Show)
data Instance = Instance { origin :: Text, arguments :: [Type], identity :: Text } deriving (Eq,Show)
data Result = Result { inventory :: Inventory, instances :: [Instance], failures :: M.Map Text Refusal
  , directRoots :: S.Set Text, runtimeClosure :: S.Set Text, openRoots :: M.Map Text Text }
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
levelParameter i = LevelExpr 0 (M.singleton i 0)
joinLevel :: LevelExpr -> LevelExpr -> LevelExpr
joinLevel (LevelExpr n xs) (LevelExpr m ys) = LevelExpr (max n m) (M.unionWith max xs ys)
shiftLevel :: Integer -> LevelExpr -> LevelExpr
shiftLevel n (LevelExpr m xs) = LevelExpr (n+m) (M.map (+n) xs)
levelNumber :: LevelExpr -> Either Refusal Integer
levelNumber (LevelExpr n xs) | M.null xs = Right n
levelNumber _ = refuse Representation "Unresolved universe level"
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
readType inv env t = case string (get "tag" t) of
  "native-open-type" -> Open <$> number (get "slot" t) <*> natural (get "universe" t)
  "native-open-family" -> do
    domains <- traverse (readType inv env) (array (get "domains" t))
    family <- OpenFamily <$> number (get "slot" t) <*> pure domains <*> natural (get "universe" t)
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
      _ -> foldM (projectIndex inv) value es
  "constructor" -> do
    let c = string (get "symbol" t)
    if c `elem` [builtin inv "zero",builtin inv "suc"] && not (T.null c)
      then readIndex inv env (Named (builtin inv "nat") []) t
      else do
        readConstructorIndex inv env Nothing t
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
      Just d | get "kind" d == String "function" -> do
        declared <- field inv "type" d
        if returnsUniverse declared then do
          unless (get "abstract" d == Bool False && get "opaque" d == Bool False && terminationChecked inv d)
            (refuse Semantics "Type alias is not transparently terminating")
          case Reduction.reduceHead inv t of
            Just (reduced,_) -> readType inv env reduced
            Nothing -> refuse Representation "Type alias requires known checked arguments"
        else readFunctionType d name es
      Just d | get "kind" d `elem` [String "record",String "datatype"] -> do
        (kinds,indices,_) <- familySignature inv d
        let count = length kinds
        unless (length es == count + length indices) (refuse Syntax "Family application arity mismatch")
        args <- readStaticArguments inv env kinds (take count es)
        domains <- traverse (substitute args) indices
        -- Later index domains may depend on earlier index values. Their
        -- telescope positions are not runtime inputs of the enclosing term.
        values <- foldM (\prior (domain,e) -> do
          let contextual = replaceInputs [ix | Runtime _ ix <- prior] domain
          value <- app e >>= readIndex inv env contextual
          pure (prior ++ [value])) [] (zip domains (drop count es))
        pure (Named name (args ++ values))
      _ -> Named name <$> traverse (app >=> readType inv env) es
  _ -> refuse Representation "Type expression is outside named first-order families"
  where
    applyFamily family domains es
      | null es = Right family
      | otherwise = do
          unless (length es == length domains) (refuse Representation "Type-family application must supply every index")
          args <- sequence [app e >>= readIndex inv env domain | (domain,e) <- zip domains es]
          applyTypeFamily family args
    readFunctionType d name es = do
        projection <- field inv "projection" d
        if get "proper" projection /= Null then case es of
          _ -> do
            position <- subtract 1 <$> number (get "index" projection)
            e <- at position es
            let rest = drop (position+1) es
            receiver <- app e >>= readType inv env
            projected <- projectIndex inv receiver (object ["tag" .= ("project" :: Text),"symbol" .= name])
            foldM (projectIndex inv) projected rest
        else do
          sig <- signature inv d
          let count = parameters sig
          unless (dropped sig <= count && length es == count + length (inputs sig))
            (refuse Representation "Computed index helper must supply its complete runtime argument list")
          args <- readStaticArguments inv env (parameterKinds sig) (take count es)
          domains <- traverse (substitute args) (inputs sig)
          out <- substitute args (output sig)
          values <- sequence [app e >>= readIndex inv env domain | (e,domain) <- zip (drop count es) domains]
          pure (Runtime out (IndexCall name args [i | Runtime _ i <- values]))

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
      value <- if get "tag" term == String "lambda" then case inputs of
        [domain] -> do
          let abstraction = get "abstraction" term
              locals = S.unions [familyLocals t | Just t <- env]
              slot = maybe 0 (+1) (S.lookupMax locals)
              context = if get "binds" abstraction == Bool True then Just (Runtime domain (IndexLocal slot)):env else env
          body <- readType inv context (get "body" abstraction)
          pure (FamilyExpression domain slot body expectedLevel)
        _ -> refuse Representation "Type-family lambda requires one first-order domain"
        else readType inv env term
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
        Runtime domain _ | domain == expected -> Right actual
        _ -> refuse Semantics "Index constructor has the wrong declared domain"
  | otherwise = do
      actual <- readType inv env term
      case actual of
        Runtime domain _ | domain == expected -> Right actual
        _ -> refuse Semantics "Index expression has the wrong declared domain"

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
  args <- traverse (\i -> maybe (refuse Representation "Cannot recover index constructor parameter") Right (M.lookup i final)) [0..parameters sig-1]
  result <- substitute args (replaceInputs payloads (output sig))
  pure (Runtime result (IndexConstructor c args
    (if get "kind" owner == String "record" then payloads else drop runtimeParameters payloads)))
  where
    step sig (known,prior) (domain,value) = do
      completed <- complete sig known
      let args = [M.findWithDefault (Parameter i) i completed | i <- [0..parameters sig-1]]
      -- Telescope indices belong to this constructor; inferred static
      -- arguments can contain indices belonging to the caller. Substitute
      -- the former before inserting the latter, keeping both scopes intact.
      concrete <- substitute args (replaceInputs prior domain)
      let contextualConstructor = get "tag" value == String "constructor" && case concrete of Named{} -> True; _ -> False
      actual <- if hasParameter concrete && not contextualConstructor then readType inv env value else readIndex inv env concrete value
      case actual of
        Runtime actualDomain ix -> do
          next <- unify completed domain actualDomain
          pure (next,prior ++ [ix])
        _ -> refuse Semantics "Constructor index payload is not a runtime value"
    hasParameter Parameter{} = True
    hasParameter FamilyParameter{} = True
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
          Just ty | closed ty -> universeOf inv ty >>= constrainLevel table level
          _ -> Right table
        step table _ = Right table

replaceInputs :: [IndexExpr] -> Type -> Type
replaceInputs values = mapIndices go
  where
    go (IndexInput i) | i < length values = values !! i
    go (IndexConstructor c ts xs) = IndexConstructor c (map (replaceInputs values) ts) (map go xs)
    go (IndexSuccessor x) = IndexSuccessor (go x)
    go (IndexProject f ts x) = IndexProject f (map (replaceInputs values) ts) (go x)
    go (IndexCall f ts xs) = IndexCall f (map (replaceInputs values) ts) (map go xs)
    go x = x

replaceKnownInputs :: M.Map Int IndexExpr -> Type -> Type
replaceKnownInputs values = mapIndices go
  where
    go original@(IndexInput i) = M.findWithDefault original i values
    go (IndexConstructor c ts xs) = IndexConstructor c (map (replaceKnownInputs values) ts) (map go xs)
    go (IndexSuccessor x) = IndexSuccessor (go x)
    go (IndexProject f ts x) = IndexProject f (map (replaceKnownInputs values) ts) (go x)
    go (IndexCall f ts xs) = IndexCall f (map (replaceKnownInputs values) ts) (map go xs)
    go x = x

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
  out <- substitute concrete (replaceInputs (contextual ++ [receiver]) (output sig))
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
            Right domain -> do
              unless (get "relevance" (get "info" dom) == String "relevant" && get "quantity" (get "info" dom) /= String "zero")
                (refuse Semantics "Erased type-family index domain")
              let next = if get "binds" cod == Bool False then context else Nothing:context
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
  (kinds,ins,out) <- go [] [] [] ty
  p <- field inv "projection" d
  dropCount <- if p == Null then Right 0 else subtract 1 <$> number (get "index" p)
  unless (dropCount >= 0 && dropCount <= length kinds + length ins) (refuse Syntax "Projection-like function drops too many arguments")
  pure (Signature (length kinds) ins out dropCount kinds)
  where
    go env kinds ins ty = let t = get "term" ty in if get "tag" t == String "pi" then do
      let dom = get "domain" t; cod = get "codomain" t
          extend x = if get "binds" cod == Bool False then env else x:env
      kind <- if null ins && toJSON (length kinds) `elem` array (get "unusedModuleParameters" d)
        then pure (Just UnusedKind) else parameterKind inv env (get "type" dom)
      case kind of
        Just k | null ins -> go (extend (Just (parameterSlot (length kinds) k))) (kinds ++ [k]) ins (get "body" cod)
        _ -> do
          let modality = get "info" dom
          unless (get "relevance" modality == String "relevant" && get "quantity" modality /= String "zero")
            (refuse Semantics "Erased or irrelevant value argument requires a separate representation rule")
          a <- readType inv env (get "term" (get "type" dom))
          go (extend (Just (Runtime a (IndexInput (length ins))))) kinds (ins ++ [a]) (get "body" cod)
      else (kinds,ins,) <$> readType inv env t

substituteLevel :: [Type] -> LevelExpr -> Either Refusal LevelExpr
substituteLevel args (LevelExpr n xs) = foldM step (levelConstant n) (M.toAscList xs)
  where
    step total (i,offset) = do
      actual <- at i args
      case actual of
        Level l -> Right (joinLevel total (shiftLevel offset l))
        _ -> refuse Semantics "Type argument used in a universe-level position"
substitute :: [Type] -> Type -> Either Refusal Type
substitute _ Unused = Right Unused
substitute args (Parameter i) = at i args
substitute _ t@Open{} = Right t
substitute args (FamilyParameter i _ _) = at i args
substitute args (OpenFamily i domains level) = OpenFamily i <$> traverse (substitute args) domains <*> pure level
substitute args (FamilyApplication family indices) = do
  actual <- substitute args family
  values <- traverse (substitute args) indices
  applyTypeFamily actual values
substitute args (FamilyExpression domain slot body level) = FamilyExpression <$> substitute args domain <*> pure slot
  <*> substitute args body <*> substituteLevel args level
substitute args (Named s ts) = Named s <$> traverse (substitute args) ts
substitute args (Level l) = Level <$> substituteLevel args l
substitute args (Runtime ty index) = Runtime <$> substitute args ty <*> go index
  where
    go (IndexProject f ts receiver) = IndexProject f <$> traverse (substitute args) ts <*> go receiver
    go (IndexCall f ts values) = IndexCall f <$> traverse (substitute args) ts <*> traverse go values
    go (IndexConstructor c ts xs) = IndexConstructor c <$> traverse (substitute args) ts <*> traverse go xs
    go (IndexSuccessor i) = IndexSuccessor <$> go i
    go i = Right i
closed :: Type -> Bool
closed Unused = True
closed Parameter{} = False
closed Open{} = True
closed FamilyParameter{} = False
closed (OpenFamily _ domains _) = all closed domains
closed (FamilyApplication family indices) = closed family && all closed indices
closed (FamilyExpression domain slot body level) = closed domain && closed (Level level)
  && closed (mapIndices erase body)
  where
    erase (IndexLocal i) | i == slot = IndexCaptured 0
    erase (IndexConstructor c ts xs) = IndexConstructor c (map (mapIndices erase) ts) (map erase xs)
    erase (IndexProject f ts x) = IndexProject f (map (mapIndices erase) ts) (erase x)
    erase (IndexCall f ts xs) = IndexCall f (map (mapIndices erase) ts) (map erase xs)
    erase (IndexSuccessor x) = IndexSuccessor (erase x)
    erase x = x
closed (Runtime ty index) = closed ty && go index
  where
    go IndexCaptured{} = True
    go IndexLocal{} = False
    go IndexInput{} = False
    go (IndexConstructor _ args xs) = all closed args && all go xs
    go (IndexProject _ ts receiver) = all closed ts && go receiver
    go (IndexCall _ ts values) = all closed ts && all go values
    go (IndexSuccessor i) = go i
    go IndexNatural{} = True
closed (Named _ ts) = all closed ts
closed (Level (LevelExpr _ xs)) = M.null xs

-- Read the actual family telescope and result universe, preserving binders
-- even when a parameter is phantom in all runtime fields.
familySignature :: Inventory -> Value -> Either Refusal ([ParameterKind],[Type],LevelExpr)
familySignature inv d = do
  n <- field inv "parameters" d >>= number
  ty <- field inv "type" d
  go [] [] n ty
  where
    go env kinds 0 ty = indices env kinds [] ty
    go env kinds n ty = do
      let t = get "term" ty; cod = get "codomain" t
      unless (get "tag" t == String "pi") (refuse Syntax "Missing carrier parameter telescope")
      kind <- if toJSON (length kinds) `elem` array (get "unusedModuleParameters" d)
        then pure (Just UnusedKind) else parameterKind inv env (get "type" (get "domain" t))
      case kind of
        Just k -> do
          let extended = if get "binds" cod == Bool False then env else Just (parameterSlot (length kinds) k):env
          go extended (kinds ++ [k]) (n-1) (get "body" cod)
        Nothing -> valueParameters env kinds [] n ty
    valueParameters env kinds ins 0 ty = indices env kinds ins ty
    valueParameters env kinds ins n ty = do
      let t = get "term" ty; cod = get "codomain" t; dom = get "domain" t
      unless (get "tag" t == String "pi") (refuse Syntax "Missing value parameter telescope")
      k <- parameterKind inv env (get "type" dom)
      unless (k == Nothing) (refuse Representation "Static parameter follows a runtime value parameter")
      a <- readType inv env (get "term" (get "type" dom))
      let extended = if get "binds" cod == Bool False then env else Just (Runtime a (IndexInput (length ins))):env
      valueParameters extended kinds (ins ++ [a]) (n-1) (get "body" cod)
    indices env kinds ins ty
      | isUniverse ty = do
          l <- readLevel inv env (get "level" (get "sort" (get "term" ty)))
          pure (kinds,ins,l)
      | otherwise = do
          let t = get "term" ty; cod = get "codomain" t; dom = get "domain" t
          unless (get "tag" t == String "pi") (refuse Representation "Unsupported carrier universe")
          unless (get "relevance" (get "info" dom) == String "relevant"
            && get "quantity" (get "info" dom) /= String "zero") (refuse Semantics "Erased family index")
          a <- readType inv env (get "term" (get "type" dom))
          let extended = if get "binds" cod == Bool False then env else Just (Runtime a (IndexInput (length ins))):env
          indices extended kinds (ins ++ [a]) (get "body" cod)

universeOf :: Inventory -> Type -> Either Refusal Integer
universeOf _ (Open _ level) = Right level
universeOf _ (FamilyApplication (OpenFamily _ _ level) _) = Right level
universeOf inv (FamilyExpression _ _ body _) = universeOf inv body
universeOf inv (Named s args) = do
  d <- maybe (refuse Syntax "Unknown concrete type universe") Right (M.lookup s (declarations inv))
  (kinds,indices,l) <- familySignature inv d
  unless (length kinds + length indices == length args) (refuse Syntax "Concrete type arity mismatch")
  substituteLevel (staticArguments args) l >>= levelNumber
universeOf _ _ = refuse Semantics "Static level is not a runtime type"

validateArguments :: Inventory -> [ParameterKind] -> [Type] -> Either Refusal ()
validateArguments inv kinds args = do
  unless (length kinds == length args && all closed args) (refuse Representation "Unresolved static arguments")
  forM_ (zip kinds args) $ \(kind,arg) -> case (kind,arg) of
    (UnusedKind,Unused) -> pure ()
    (LevelKind,Level l) -> () <$ levelNumber l
    (TypeKind expected,t) | case t of Named{} -> True; Open{} -> True; FamilyApplication{} -> True; _ -> False -> do
      actual <- universeOf inv arg
      resolved <- substituteLevel args expected >>= levelNumber
      unless (actual == resolved) (refuse Semantics "Concrete type argument has the wrong universe")
    (FamilyKind domains level,OpenFamily _ actualDomains actualLevel) -> do
      expectedDomains <- traverse (substitute args) domains
      expectedLevel <- substituteLevel args level >>= levelNumber
      unless (actualDomains == expectedDomains && actualLevel == expectedLevel)
        (refuse Semantics "Type-family argument has incompatible index domains or universe")
    (FamilyKind domains level,FamilyExpression domain _ body actualLevel) -> do
      expectedDomains <- traverse (substitute args) domains
      expectedLevel <- substituteLevel args level >>= levelNumber
      actual <- universeOf inv body
      declared <- levelNumber actualLevel
      unless (expectedDomains == [domain] && expectedLevel == actual && declared == actual)
        (refuse Semantics "Type-family lambda has incompatible domain or universe")
    _ -> refuse Semantics "Static level/type argument kind mismatch"

-- Solve only a uniquely determined level. Non-injective maxima remain
-- pending until other arguments determine them; no arbitrary level is chosen.
constrainLevel :: M.Map Int Type -> LevelExpr -> Integer -> Either Refusal (M.Map Int Type)
constrainLevel known (LevelExpr n xs) target = do
  partial <- foldM collect (levelConstant n) (M.toList xs)
  let LevelExpr c remaining = partial
  unless (c <= target && all (<= target) (M.elems remaining)) (refuse Semantics "Inconsistent universe-level constraint")
  case M.toList remaining of
    [] -> if c == target then Right known else refuse Semantics "Universe-level mismatch"
    [(i,offset)] | c < target || offset == target -> Right (M.insert i (Level (levelConstant (target-offset))) known)
    _ -> Right known
  where
    collect total (i,offset) = case M.lookup i known of
      Nothing -> Right (joinLevel total (shiftLevel offset (levelParameter i)))
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
      Just t -> universeOf inv t >>= constrainLevel table l
      Nothing -> Right table
    step table _ = Right table

typeValue :: Type -> Value
typeValue Unused = object ["unusedModuleParameter" .= True]
typeValue (Level (LevelExpr n xs)) = if M.null xs then object ["level" .= n]
  else object ["levelConstant" .= n,"levelParameters" .= M.toAscList xs]
typeValue (Parameter i) = object ["parameter" .= i]
typeValue (Open i level) = object ["openParameter" .= i,"universe" .= level]
typeValue (FamilyParameter i domains level) = object ["familyParameter" .= i,"domains" .= map typeValue domains,"level" .= typeValue (Level level)]
typeValue t@(OpenFamily i domains level) = object ["openFamily" .= i,"domains" .= map typeValue domains,"universe" .= level,"familySymbol" .= typeKey t]
typeValue (FamilyApplication family indices) = object ["family" .= typeValue family,"indices" .= map typeValue indices]
typeValue family@FamilyExpression{} = case canonicalFamilies family of
  FamilyExpression domain slot body level -> object ["familyExpression" .= object
    ["domain" .= typeValue domain,"slot" .= slot,"body" .= typeValue body,"level" .= typeValue (Level level)]]
  _ -> Null
typeValue (Runtime ty index) = object ["runtimeType" .= typeValue ty,"index" .= indexValue index]
typeValue (Named s ts) = object ["symbol" .= s,"arguments" .= map typeValue ts]
indexValue :: IndexExpr -> Value
indexValue (IndexInput i) = object ["input" .= i]
indexValue (IndexCaptured i) = object ["capture" .= i]
indexValue (IndexLocal i) = object ["familyInput" .= i]
indexValue (IndexNatural n) = object ["natural" .= n]
indexValue (IndexSuccessor i) = object ["successor" .= indexValue i]
indexValue (IndexConstructor c args values) = object (["constructor" .= c,"arguments" .= map typeValue args]
  ++ ["values" .= map indexValue values | not (null values)])
indexValue (IndexCall f args values) = object
  ["calculation" .= f,"arguments" .= map typeValue args,"values" .= map indexValue values]
indexValue (IndexProject f args receiver) = object
  ["projection" .= f,"arguments" .= map typeValue args,"receiver" .= indexValue receiver]
instanceKey :: Text -> [Type] -> Text
instanceKey s [] = s
instanceKey s ts = s <> "@" <> digest (BL.toStrict (encode (object ["symbol" .= s,"arguments" .= map typeValue (fst (captureArguments ts))])))
typeKey :: Type -> Text
typeKey Unused = "$unused-module-parameter"
typeKey (Named s ts) = instanceKey s (staticArguments ts)
typeKey (Level (LevelExpr n _)) = "level:" <> T.pack (show n)
typeKey Runtime{} = "runtime-index-has-no-static-key"
typeKey (Parameter i) = "unresolved-parameter-" <> T.pack (show i)
typeKey (Open i level) = "$native-type-parameter:" <> T.pack (show i) <> ":" <> T.pack (show level)
typeKey (FamilyParameter i _ _) = "unresolved-family-" <> T.pack (show i)
typeKey (OpenFamily i domains level) = "$native-type-family:" <> T.pack (show i) <> ":"
  <> digest (BL.toStrict (encode (map typeValue domains,level)))
typeKey (FamilyApplication family _) = typeKey family
typeKey family@FamilyExpression{} = "$native-family-expression:" <> digest (BL.toStrict (encode (typeValue family)))

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
typeTerm depth ty@(Named _ args) = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty
  ,"eliminations" .= [application (indexTerm depth i) | i <- map snd (snd (captureArguments (staticArguments args))) ++ [ix | Runtime _ ix <- args]]]
typeTerm depth ty@(FamilyApplication _ args) = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty
  ,"eliminations" .= [application (indexTerm depth i) | Runtime _ i <- args]]
typeTerm _ ty = object ["tag" .= ("definition" :: Text),"symbol" .= typeKey ty,"eliminations" .= ([] :: [Value])]
indexTerm :: Int -> IndexExpr -> Value
indexTerm depth (IndexCaptured i) = indexTerm depth (IndexInput i)
indexTerm _ (IndexLocal _) = object ["tag" .= ("unbound-family-input" :: Text)]
indexTerm depth (IndexInput i) = object ["tag" .= ("variable" :: Text),"index" .= (depth-i-1),"eliminations" .= ([] :: [Value])]
indexTerm _ (IndexNatural n) = object ["tag" .= ("literal" :: Text),"literal" .= object ["tag" .= ("natural" :: Text),"value" .= n]]
indexTerm depth (IndexSuccessor i) = object ["tag" .= ("native-index-successor" :: Text),"predecessor" .= indexTerm depth i]
indexTerm depth (IndexConstructor c args values) = object ["tag" .= ("constructor" :: Text),"symbol" .= instanceKey c args
  ,"eliminations" .= map (application . indexTerm depth) values]
indexTerm depth (IndexCall f args values) = object ["tag" .= ("definition" :: Text),"symbol" .= instanceKey f args
  ,"eliminations" .= map (application . indexTerm depth) values]
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
prepare source | not active = Result source [] M.empty roots S.empty M.empty
            | otherwise = Result expanded entries errors roots runtime open
  where
    inv = UnusedParameters.annotate source
    needs = required inv
    active = any (\(s,r) -> r `elem` ["structure","behavior"] && generic s
      || r == "behavior" && callbackSignature s) (S.toList needs)
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
            _ -> False)
        _ -> False
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
              TypeKind level -> Open i <$> liftEither (substituteLevel prior level >>= levelNumber)
              FamilyKind domains level -> OpenFamily i <$> liftEither (traverse (substitute prior) domains)
                <*> liftEither (substituteLevel prior level >>= levelNumber)
              LevelKind -> abort Representation "Open universe-level parameters require a separate representation rule"
            pure (prior ++ [arg])) [] (zip [0..] kinds)
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
    (attempts,store) = runState action (Store M.empty M.empty)
    errors = M.fromList [(s,e) | (s,Left e) <- attempts]
    open = M.fromList [(s,key) | (s,Right key) <- attempts,generic s,openProfile,S.member s roots]
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
showType _ Unused = "unused module parameter"
showType _ (Level (LevelExpr n xs)) = if M.null xs then "level " <> T.pack (show n) else "unresolved level"
showType inv (Runtime _ index) = showIndex index
  where
    showIndex (IndexCaptured i) = "captured index " <> T.pack (show i)
    showIndex (IndexLocal i) = "family input " <> T.pack (show i)
    showIndex (IndexInput i) = "input" <> T.pack (show i)
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
      $ set "specializationArguments" (toJSON (map typeValue (fst (captureArguments args)))) d) (ready st)
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
  when (M.member key (declarations inv)) (abort Syntax "Native family identity collides with a source declaration")
  unless (not (null domains) && all closed domains) (abort Representation "Type-family domains must be independently bound first-order carriers")
  mapM_ (ensureType inv stack) domains
  modify' $ \st -> st {ready = M.insert key (object ["name" .= key,"displayName" .= ("type family " <> T.pack (show slot))
    ,"kind" .= ("native-family-parameter" :: Text),"nativeFamily" .= slot,"familyDomains" .= map (asType 0) domains
    ,"specializationArguments" .= [typeValue family],"universe" .= level]) (ready st)}
ensureType inv _ ty@(Open i level) = do
  let key = typeKey ty
  when (M.member key (declarations inv)) (abort Syntax "Native parameter identity collides with a source declaration")
  modify' $ \st -> st {ready = M.insert key (object ["name" .= key
    ,"kind" .= ("native-type-parameter" :: Text),"nativeParameter" .= i,"universe" .= level]) (ready st)}
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
      _ -> abort Representation "List requires a closed level and element type"
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
      captureTypes = map fst captures
      prefix = length captures
      instantiate sourceType = substitute schemaArgs (shiftIndices prefix sourceType)
  unless (all closed args) (abort Representation "Carrier specialization requires concrete static arguments")
  forM_ args $ \arg -> case arg of Level{} -> pure (); Unused -> pure (); _ -> ensureType inv stack arg
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
    let header = set "type" (telescope indexTypes (object ["term" .= object ["tag" .= ("sort" :: Text)]]))
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
        (abort Semantics "Constructor result has wrong family or index arity")
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
    let d' = set "type" (telescope indexTypes (object ["term" .= object ["tag" .= ("sort" :: Text)]]))
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
ensureIndex inv (IndexConstructor _ _ xs) = mapM_ (ensureIndex inv) xs
ensureIndex _ _ = pure ()

-- The compiled value environment is independent of type-codomain binding.
data Binding = Static Type | Dynamic Type deriving (Eq,Show)
isDynamic :: Binding -> Bool
isDynamic Dynamic{} = True
isDynamic _ = False

ensureFunction :: Inventory -> [Text] -> Text -> [Type] -> Build ()
ensureFunction inv stack s actualArgs = do
  let (args,captures) = captureArguments actualArgs
      prefix = length captures
      captureTypes = map fst captures
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
          let env = map Dynamic captureTypes ++ drop (dropped sig) (map Static schemaArgs ++ map Dynamic (drop prefix ins))
          specializeTree inv (s:stack) env out (prefixTree prefix tree)) `catchError` \reason -> do
            modify' $ \st -> st {ready = M.delete (instanceKey s args) (ready st), recorded = M.delete (instanceKey s args) (recorded st)}
            throwError (context ("Specializing " <> s <> ": ") reason)
        let d' = set "type" (arrow ins out) $ set "compiled" body $ set "projection"
              (if dropped sig > parameters sig then set "index" (toJSON (dropped sig - parameters sig + 1)) p else Null)
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
specializeTree inv stack env out tree = case string (get "tag" tree) of
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
      body <- specializeTree inv stack env result (get "tree" b)
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
              rewrite x = x
              bindings = map rewrite contextual ++ payloadIndices
              change (Dynamic domain) = Dynamic (reindex domain)
              change binding = binding
          fields <- liftEither (traverse (substitute (map reindex args) . replaceInputs bindings) fieldSchemas)
          arity <- liftEither (number (get "arity" b))
          unless (arity == length fields) (abort Syntax "Specialized case payload arity mismatch")
          result <- specializeTree inv stack (map change (take i env) ++ map Dynamic fields ++ map change (drop (i+1) env))
            (reindex out) (get "tree" b)
          pure (set "tree" result b)
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
      else specializeTree inv stack env out (get "catchall" tree)
    -- Literal and copattern modes remain visible to the native rule gate.
    pure $ set "argument" (set "value" (toJSON (length (filter isDynamic (take i env)))) (get "argument" tree))
      $ set "constructors" (toJSON cs) $ set "eta" eta' $ set "catchall" catchall tree
  _ -> abort Syntax "Specialization requires a supported finite compiled body"

unify :: M.Map Int Type -> Type -> Type -> Either Refusal (M.Map Int Type)
unify known Unused Unused = Right known
unify known (Level l) (Level actual) = levelNumber actual >>= constrainLevel known l
-- This pass infers only static substitutions. Runtime equalities are retained
-- in serialized signatures and checked by AlgebraicTarget after specialization.
-- Varying runtime indices share a family instance; fixed fibres used as static
-- type arguments still retain their indices in the outer instance identity.
unify known (Runtime domain _) (Runtime actual _) = unify known domain actual
unify known (Parameter i) actual = case M.lookup i known of
  Nothing -> Right (M.insert i actual known)
  Just t | t == actual -> Right known
  _ -> refuse Semantics ("Inconsistent concrete type arguments: " <> T.pack (show (M.lookup i known,actual)))
unify known (Open i l) (Open j m) | i == j && l == m = Right known
-- Signature inference may compare a family before its open binding is known.
-- Recover the omitted argument even when it remains symbolic; equality
-- preserves its lexical identity, domain and universe. This neither invents
-- a concrete binding nor discharges a runtime index equality.
unify known a@(FamilyParameter i _ _) b@FamilyParameter{} | a == b = unify known (Parameter i) b
unify known (FamilyParameter i _ _) actual@OpenFamily{} = unify known (Parameter i) actual
unify known (FamilyParameter i _ _) actual@FamilyExpression{} = unify known (Parameter i) actual
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
    sourceTypeAt depth (Named s args) = object ["term" .= object ["tag" .= ("definition" :: Text)
      ,"symbol" .= s,"eliminations" .= map (application . get "term" . sourceTypeAt depth) args]]
    sourceTypeAt _ (Open slot level) = object ["term" .= object ["tag" .= ("native-open-type" :: Text)
      ,"slot" .= slot,"universe" .= level]]
    sourceTypeAt depth (OpenFamily slot domains level) = object ["term" .= object ["tag" .= ("native-open-family" :: Text)
      ,"slot" .= slot,"domains" .= map (get "term" . sourceTypeAt depth) domains,"universe" .= level]]
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
        [object ["offset" .= offset,"term" .= Reduction.variable i] | (i,offset) <- M.toAscList terms]]]]
    sourceTypeAt depth t = asType depth t
    sourceIndex depth (IndexConstructor c _ values) = object ["tag" .= ("constructor" :: Text)
      ,"symbol" .= c,"eliminations" .= map (application . sourceIndex depth) values]
    sourceIndex depth (IndexNatural value) = indexTerm depth (IndexNatural value)
    sourceIndex depth (IndexSuccessor value) = object ["tag" .= ("constructor" :: Text)
      ,"symbol" .= builtin inv "suc","eliminations" .= [application (sourceIndex depth value)]]
    sourceIndex depth (IndexCall f types values) = object ["tag" .= ("definition" :: Text),"symbol" .= f
      ,"eliminations" .= map application (map (get "term" . sourceTypeAt depth) types ++ map (sourceIndex depth) values)]
    sourceIndex depth (IndexProject f types receiver) = object ["tag" .= ("definition" :: Text),"symbol" .= f
      ,"eliminations" .= map application (map (get "term" . sourceTypeAt depth) types ++ [sourceIndex depth receiver])]
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
    normal (FamilyApplication f xs) = FamilyApplication (normal f) (map normal xs)
    normal (OpenFamily i xs l) = OpenFamily i (map normal xs) l
    normal (Runtime domain ix) =
      let ty = Runtime (normal domain) ix
      in case Reduction.reduceHead inv (get "term" (sourceTypeTerm inv depth ty)) of
        Just (reduced,_) -> either (const ty) id (readIndex inv env (normal domain) reduced)
        Nothing -> ty
    normal t = t

expression :: Inventory -> [Text] -> [Binding] -> Maybe Type -> Value -> Build (Type,Value)
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
        schemaOut <- liftEither (substitute tyArgs (replaceKnownInputs indices (output sig)))
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
      "definition" -> do
        let s = string (get "symbol" term)
        d <- definition inv s
        unless (get "kind" d `elem` [String "function",String "primitive"]) (abort Semantics "Runtime call is not a checked function")
        sig <- liftEither (either (Left . context ("Signature of " <> s <> ": ")) Right (signature inv d))
        let supplied = max 0 (parameters sig - dropped sig)
        unless (length es >= supplied) (abort Representation "Partially applied type parameters")
        actualTypes <- liftEither (sequence [if kind == UnusedKind then app e >> pure Unused
          else app e >>= readType inv (runtimeBindings env)
          | (kind,e) <- zip (drop (min (parameters sig) (dropped sig)) (parameterKinds sig)) (take supplied es)])
        let explicit = M.fromList (zip [min (parameters sig) (dropped sig)..] actualTypes)
            valueElims = drop supplied es
        known <- if length valueElims == length (inputs sig) then
          maybe (pure explicit) (liftEither . unifyIn inv env explicit (output sig)) expected else pure explicit
        let runtimeDropped = max 0 (dropped sig - parameters sig)
        (types,values,indices,rest) <- argumentsFor (sig {inputs = drop runtimeDropped (inputs sig)}) runtimeDropped [] known valueElims
        ensureFunction inv stack s types
        out <- liftEither (substitute types (replaceKnownInputs indices (output sig)))
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
          let fill t = case substitute [M.findWithDefault (Parameter i) i known | i <- [0..parameters sig-1]] (replaceKnownInputs indices t) of
                Right actual | resolved actual -> Just actual
                _ -> Nothing
              resolved Parameter{} = False
              resolved FamilyParameter{} = False
              resolved (Named _ ts) = all resolved ts
              resolved (FamilyApplication f xs) = all resolved (f:xs)
              resolved (FamilyExpression domain _ body level) = resolved domain && resolved body && closed (Level level)
              resolved (OpenFamily _ xs _) = all resolved xs
              resolved (Runtime domain index) = resolved domain && resolvedIndex index
              resolved t = closed t
              resolvedIndex (IndexConstructor _ ts xs) = all resolved ts && all resolvedIndex xs
              resolvedIndex (IndexProject _ ts x) = all resolved ts && resolvedIndex x
              resolvedIndex (IndexCall _ ts xs) = all resolved ts && all resolvedIndex xs
              resolvedIndex (IndexSuccessor x) = resolvedIndex x
              resolvedIndex _ = True
          (actual,v) <- expression inv stack env (fill patternType) value
          known' <- liftEither (unifyIn inv env known patternType actual)
          completed <- liftEither (completeKnown inv sig known')
          let concrete = substitute [M.findWithDefault (Parameter i) i completed | i <- [0..parameters sig-1]]
                (replaceKnownInputs indices patternType)
              index = concrete >>= \domain -> readIndex inv (runtimeBindings env) domain value
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
            ,"captures" .= map typeValue (take (length captures) allTypes),"types" .= map typeValue (resultType:allTypes)]) d
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
