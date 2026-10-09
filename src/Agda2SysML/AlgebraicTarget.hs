{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Closed, acyclic products and sums. Every payload position is retained;
-- named types, constructor identities and projections come from checked Agda.
module Agda2SysML.AlgebraicTarget
  ( Carrier(..), Shape(..), pattern Shape, Constructor(..), Calculation(..), Expression(Input, Literal, NumberLiteral, Numeric, Sequence, SequenceOp, SequenceHead, Enumeration, Construct, Project, Equal, Conditional, Call, Absent)
  , discover, function, symbols, renderShapes, renderShapesIn, renderCalculation, renderCalculationDoc, references
  , constructorCalculations, naturalCalculations, generatedNames, carrierReport, functions, calls, calculationContracts, calculationContractsIn, dependencies ) where

import qualified Agda2SysML.Derivation as D
import Agda2SysML.Inventory hiding (field)
import Agda2SysML.Diagnostic (Refusal, Category(..), refuse, refusal, context, field)
import qualified Agda2SysML.FiniteTarget as F
import qualified Agda2SysML.Specialize as Specialize
import Control.Monad (unless, forM, foldM, (>=>))
import Data.Graph (SCC(..), stronglyConnComp)
import Data.Aeson
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger, floatingOrInteger)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

data Carrier = Boolean | Natural | AnyValue | TypeParameter Int | Named Text | Fibre Text [Expression] deriving (Eq, Show)
data Constructor = Constructor
  { constructorSymbol :: Text, payload :: [(Text,Carrier)], resultIndices :: [Expression] } deriving (Eq, Show)
data Shape = ShapeData
  { shapeSymbol :: Text, isRecord :: Bool, variants :: [Constructor], indexTypes :: [Carrier]
  , sequenceElement :: Maybe Carrier, typeParameters :: [Int]
  , familyParameters :: [(Int,Text)], relationParameter :: Maybe Int, recursivePeers :: [Text] } deriving (Eq, Show)
pattern Shape :: Text -> Bool -> [Constructor] -> [Carrier] -> Shape
pattern Shape s r cs is <- ShapeData s r cs is _ _ _ _ _ where Shape s r cs is = ShapeData s r cs is Nothing [] [] Nothing []
data Expression = Annotated D.Origin Expression
  | NInput Int
  | NLiteral Bool
  | NNumberLiteral Integer
  | NNumeric Text Expression Expression
  | NSequence [Expression]
  | NSequenceOp Text Expression
  | NSequenceHead Carrier Expression
  | NEnumeration Text Text
  | NConstruct Text [(Text,Expression)]
  | NProject Expression Text
  | NEqual Expression Expression
  | NConditional Expression Expression Expression
  | NCall Text [Expression]
  | NBoundCall Text [Text] [Expression]
  | NAbsent
  deriving Show

unmark :: Expression -> Expression
unmark (Annotated _ x) = unmark x
unmark x = x

instance Eq Expression where
  x == y | NInput a0 <- unmark x, NInput b0 <- unmark y = a0 == b0
  x == y | NLiteral a0 <- unmark x, NLiteral b0 <- unmark y = a0 == b0
  x == y | NNumberLiteral a <- unmark x, NNumberLiteral b <- unmark y = a == b
  x == y | NNumeric op a b <- unmark x, NNumeric op' a' b' <- unmark y = (op,a,b) == (op',a',b')
  x == y | NSequence xs <- unmark x, NSequence ys <- unmark y = xs == ys
  x == y | NSequenceOp op a <- unmark x, NSequenceOp op' b <- unmark y = (op,a) == (op',b)
  x == y | NSequenceHead t a <- unmark x, NSequenceHead u b <- unmark y = (t,a) == (u,b)
  x == y | NEnumeration a0 a1 <- unmark x, NEnumeration b0 b1 <- unmark y = a0 == b0 && a1 == b1
  x == y | NConstruct a0 a1 <- unmark x, NConstruct b0 b1 <- unmark y = a0 == b0 && a1 == b1
  x == y | NProject a0 a1 <- unmark x, NProject b0 b1 <- unmark y = a0 == b0 && a1 == b1
  x == y | NEqual a0 a1 <- unmark x, NEqual b0 b1 <- unmark y = a0 == b0 && a1 == b1
  x == y | NConditional a0 a1 a2 <- unmark x, NConditional b0 b1 b2 <- unmark y = a0 == b0 && a1 == b1 && a2 == b2
  x == y | Just (a0,a1) <- callParts x, Just (b0,b1) <- callParts y = a0 == b0 && a1 == b1
  x == y | NAbsent <- unmark x, NAbsent <- unmark y = True
  _ == _ = False
pattern Input :: Int -> Expression
pattern Input i <- (unmark -> NInput i) where Input i = NInput i
pattern Literal :: Bool -> Expression
pattern Literal b <- (unmark -> NLiteral b) where Literal b = NLiteral b
pattern NumberLiteral :: Integer -> Expression
pattern NumberLiteral n <- (unmark -> NNumberLiteral n) where NumberLiteral n = NNumberLiteral n
pattern Numeric :: Text -> Expression -> Expression -> Expression
pattern Numeric op x y <- (unmark -> NNumeric op x y) where Numeric op x y = NNumeric op x y
pattern Sequence :: [Expression] -> Expression
pattern Sequence xs <- (unmark -> NSequence xs) where Sequence xs = NSequence xs
pattern SequenceOp :: Text -> Expression -> Expression
pattern SequenceOp op xs <- (unmark -> NSequenceOp op xs) where SequenceOp op xs = NSequenceOp op xs
pattern SequenceHead :: Carrier -> Expression -> Expression
pattern SequenceHead t xs <- (unmark -> NSequenceHead t xs) where SequenceHead t xs = NSequenceHead t xs
pattern Enumeration :: Text -> Text -> Expression
pattern Enumeration s c <- (unmark -> NEnumeration s c) where Enumeration s c = NEnumeration s c
pattern Construct :: Text -> [(Text,Expression)] -> Expression
pattern Construct s fs <- (unmark -> NConstruct s fs) where Construct s fs = NConstruct s fs
pattern Project :: Expression -> Text -> Expression
pattern Project x f <- (unmark -> NProject x f) where Project x f = NProject x f
pattern Equal :: Expression -> Expression -> Expression
pattern Equal x y <- (unmark -> NEqual x y) where Equal x y = NEqual x y
pattern Conditional :: Expression -> Expression -> Expression -> Expression
pattern Conditional p x y <- (unmark -> NConditional p x y) where Conditional p x y = NConditional p x y
pattern Call :: Text -> [Expression] -> Expression
pattern Call s xs <- (callParts -> Just (s,xs)) where Call s xs = NCall s xs
pattern BoundCall :: Text -> [Text] -> [Expression] -> Expression
pattern BoundCall s bindings xs <- (unmark -> NBoundCall s bindings xs) where BoundCall s bindings xs = NBoundCall s bindings xs

callParts :: Expression -> Maybe (Text,[Expression])
callParts expression = case unmark expression of
  NCall s xs -> Just (s,xs)
  NBoundCall s _ xs -> Just (s,xs)
  _ -> Nothing
pattern Absent :: Expression
pattern Absent <- (unmark -> NAbsent) where Absent = NAbsent
{-# COMPLETE Input, Literal, NumberLiteral, Numeric, Sequence, SequenceOp, SequenceHead, Enumeration, Construct, Project, Equal, Conditional, Call, Absent #-}

annotation :: Expression -> D.Origin
annotation (Annotated o _) = o
annotation _ = D.generated "native.generated-expression"

located :: Text -> Value -> Value -> Expression -> Expression
-- A fresh root gets its first justified origin here. Existing annotations,
-- including explicit unavailable boundaries, must survive unchanged as premises.
located rule input premises e = Annotated (D.origin rule input premises parents) e
  where parents = case e of Annotated o _ -> [o]; _ -> []

data Calculation = Calculation
  { calculationSymbol :: Text, inputs :: [Carrier], result :: Carrier, body :: Expression
  , staticIndexEquations :: [(Carrier,Expression,Expression)] }
  deriving (Eq, Show)

retain :: Text -> Expression -> Expression -> Expression
retain rule before after = Annotated (D.derived rule [] Null (origins before ++ origins after)) after
  where
    origins e = annotation e : case e of
      Construct _ fs -> concatMap (origins . snd) fs
      Project x _ -> origins x
      Equal x y -> origins x ++ origins y
      Numeric _ x y -> origins x ++ origins y
      Sequence xs -> concatMap origins xs
      SequenceOp _ xs -> origins xs
      SequenceHead _ xs -> origins xs
      Conditional p x y -> origins p ++ origins x ++ origins y
      Call _ xs -> concatMap origins xs
      _ -> []

type Helpers = M.Map Text Calculation

type Shapes = M.Map Text Shape

builtin :: Inventory -> Text -> Text
builtin inv key = string (get key (get "builtins" (document inv)))

integer :: Value -> Either Refusal Int
integer (Number n) = maybe (refuse Syntax "Invalid checked index") Right (toBoundedInteger n)
integer _ = refuse Syntax "Missing checked index"

at :: Int -> [a] -> Either Refusal a
at i xs = case drop i xs of
  x:_ | i >= 0 -> Right x
  _ -> refuse Syntax "Reference is outside its checked binding environment"

-- Types retain runtime index expressions in the lexical input environment.
carrierIn :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> [(Carrier,Expression)] -> Value -> Either Refusal Carrier
carrierIn inv finite helpers shapes env ty = do
  let t = get "term" ty; s = string (get "symbol" t)
  unless (get "tag" t == String "definition") (refuse Representation "Unsupported dependent carrier expression")
  args <- traverse applicationValue (array (get "eliminations" t))
  case M.lookup s shapes of
    Just sh | not (null (indexTypes sh)) -> do
      if null args && isRecord sh && maybe False
        (\d -> get "nativeRecordCaptures" d == toJSON (length (indexTypes sh))) (M.lookup s (declarations inv))
        then Right (Named s)
        else do
          unless (length args == length (indexTypes sh)) (refuse Syntax "Family index arity mismatch")
          values <- foldM (\prior (domain,arg) -> do
            value <- indexExpression inv finite helpers shapes env (mapCarrier (instantiate prior) domain) arg
            pure (prior ++ [value])) [] (zip (indexTypes sh) args)
          pure (Fibre s values)
    _ | not (null args) -> refuse Representation "Unadmitted indexed or parameterized carrier"
      | Just d <- M.lookup s (declarations inv),get "kind" d == String "native-type-parameter" ->
          TypeParameter <$> integer (get "nativeParameter" d)
      | s == builtin inv "bool" && not (T.null s) -> Right Boolean
      | s == builtin inv "nat" && not (T.null s) -> Right Natural
      | M.member s finite || M.member s shapes -> Right (Named s)
      | otherwise -> refuse Representation "Field/input/result needs an admitted carrier"

applicationValue :: Value -> Either Refusal Value
applicationValue e | get "tag" e == String "apply" = Right (get "value" (get "argument" e))
                   | otherwise = refuse Syntax "Index is not an application"

indexExpression :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> [(Carrier,Expression)] -> Carrier -> Value -> Either Refusal Expression
indexExpression inv finite helpers shapes env expected t = do
  (actual,e) <- infer t
  unless (actual == expected) (refuse Semantics "Index expression has the wrong admitted domain")
  pure (normalize e)
  where
    projections = projectionTable shapes
    infer term = fmap (\(typ,e) -> (typ,located "native.index-term" term (toJSON [renderWith id (T.pack . show) x | (_,x) <- env]) e)) $ do
      let es = array (get "eliminations" term)
      case string (get "tag" term) of
        "native-index-successor" -> do
          (typ,value) <- infer (get "predecessor" term)
          unless (typ == Natural) (refuse Semantics "Successor index is not natural")
          pure (Natural,Numeric "+" value (NumberLiteral 1))
        "literal" | get "tag" (get "literal" term) == String "natural" -> do
          n <- case get "value" (get "literal" term) of
            Number n -> case floatingOrInteger n :: Either Double Integer of Right k | k >= 0 -> Right k; _ -> refuse Syntax "Invalid natural index"
            _ -> refuse Syntax "Missing natural index"
          pure (Natural,NumberLiteral n)
        "variable" -> integer (get "index" term) >>= (\i -> at i env) >>= (\v -> eliminate v es)
        "constructor" | get "symbol" term == String (builtin inv "zero") && not (T.null (builtin inv "zero")) -> do
          unless (null es) (refuse Syntax "Applied zero index")
          pure (Natural,NumberLiteral 0)
        "constructor" | get "symbol" term == String (builtin inv "suc") && not (T.null (builtin inv "suc")) -> do
          args <- traverse applicationValue es
          case args of
            [arg] -> do
              (typ,value) <- infer arg
              unless (typ == Natural) (refuse Semantics "Successor index is not natural")
              pure (Natural,Numeric "+" value (NumberLiteral 1))
            _ -> refuse Syntax "Successor index arity mismatch"
        "constructor" -> do
          let c = string (get "symbol" term)
          case M.lookup c (constructorTable shapes) of
            Just (sh,con) -> do
              parameterCount <- case M.lookup c (declarations inv) of
                Just def | get "runtimeParameters" def /= Null -> integer (get "runtimeParameters" def)
                _ -> Right 0
              prefix <- if parameterCount == 0 then pure [] else case expected of
                Fibre owner indices | owner == shapeSymbol sh && length indices >= parameterCount -> pure (take parameterCount indices)
                _ -> refuse Representation "Structured index constructor needs its contextual value parameters"
              let supplied = drop parameterCount (payload con)
              unless (length es == length supplied) (refuse Syntax "Structured index constructor arity mismatch")
              values <- foldM (\prior ((_,typ),arg) -> do
                value <- applicationValue arg >>= indexExpression inv finite helpers shapes env (mapCarrier (instantiate prior) typ)
                pure (prior ++ [value])) prefix (zip supplied es)
              pure (familyCarrier sh (map (instantiate values) (resultIndices con)),
                Construct (shapeSymbol sh) (construction (Just term) sh con values))
            Nothing -> do
              unless (null es) (refuse Representation "Unadmitted index constructor has arguments")
              if c == builtin inv "true" then Right (Boolean,Literal True)
              else if c == builtin inv "false" then Right (Boolean,Literal False)
              else case [F.domainSymbol d | d <- M.elems finite,c `elem` F.constructors d] of
                [owner] -> Right (Named owner,Enumeration owner c)
                _ -> refuse Representation "Index constructor has no admitted domain"
        "definition" -> case M.lookup (string (get "symbol" term)) helpers of
          Just helper -> do
            unless (length es == length (inputs helper)) (refuse Syntax "Computed index helper arity mismatch")
            args <- foldM (\prior (domain,arg) -> do
              value <- applicationValue arg >>= infer
              unless (fst value == mapCarrier (instantiate (map snd prior)) domain)
                (refuse Semantics "Computed index helper argument domain mismatch")
              pure (prior ++ [value])) [] (zip (inputs helper) es)
            let bindings = case M.lookup (calculationSymbol helper) (declarations inv) of
                  Just def -> map parameterName (Specialize.nativeParameters def)
                    ++ map (familyName . fst) (Specialize.nativeFamilies def)
                  Nothing -> []
            pure (mapCarrier (instantiate (map snd args)) (result helper),BoundCall (calculationSymbol helper) bindings (map snd args))
          Nothing -> case es of
            arg:rest -> do
              receiver <- applicationValue arg >>= infer
              projected <- project receiver (string (get "symbol" term))
              eliminate projected rest
            _ -> refuse Representation "Computed index requires an admitted finite helper or proper record projection"
        _ -> refuse Syntax "Unsupported finite index expression"
    eliminate value [] = Right value
    eliminate value (e:es) = do
      unless (get "tag" e == String "project") (refuse Syntax "Computed index elimination")
      projected <- project value (string (get "symbol" e))
      eliminate projected es
    project (actual,value) f = do
      (owner,typ) <- maybe (refuse Representation "Index function is not an admitted proper projection") Right (M.lookup f projections)
      unless (recordOwner actual owner) (refuse Semantics "Index projection belongs to another record")
      d <- maybe (refuse Syntax "Missing index projection declaration") Right (M.lookup f (declarations inv))
      p <- field inv "projection" d
      unless (get "proper" p == String owner && get "index" p == Number 1)
        (refuse Syntax "Index expression uses invalid projection metadata")
      pure (projectedCarrier shapes actual value typ,Project value f)

finiteIndex :: M.Map Text F.Domain -> Carrier -> Bool
finiteIndex _ Boolean = True
finiteIndex finite (Named s) = M.member s finite
finiteIndex _ _ = False

-- The context of a NoAbs codomain does not acquire the preceding input.
typedTelescope :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> Value -> Either Refusal ([Carrier],[(Carrier,Expression)],Value)
typedTelescope inv finite helpers shapes = go [] []
  where
    go inputs' env ty = let t = get "term" ty in
      if get "tag" t /= String "pi" then Right (inputs',env,ty) else do
        let dom = get "domain" t; cod = get "codomain" t; modality = get "info" dom
        unless (get "relevance" modality == String "relevant" && get "quantity" modality /= String "zero")
          (refuse Semantics "Erased/irrelevant runtime binder")
        typ <- carrierIn inv finite helpers shapes env (get "type" dom)
        let next = if get "binds" cod == Bool False then env else (typ,Input (length inputs')):env
        go (inputs' ++ [typ]) next (get "body" cod)

mapExpression :: (Expression -> Maybe Expression) -> Expression -> Expression
mapExpression replace e = retain "native.substitution" e $ case replace e of
  Just v -> v
  Nothing -> case e of
    Construct s fs -> Construct s [(f,go x) | (f,x) <- fs]
    Project x f -> Project (go x) f
    Equal x y -> Equal (go x) (go y)
    Numeric op x y -> Numeric op (go x) (go y)
    Sequence xs -> Sequence (map go xs)
    SequenceOp op xs -> SequenceOp op (go xs)
    SequenceHead t xs -> SequenceHead (mapCarrier go t) (go xs)
    Conditional p x y -> Conditional (go p) (go x) (go y)
    BoundCall s bindings xs -> BoundCall s bindings (map go xs)
    Call s xs -> Call s (map go xs)
    _ -> e
  where go = mapExpression replace

mapCarrier :: (Expression -> Expression) -> Carrier -> Carrier
mapCarrier f (Fibre s xs) = Fibre s (map (normalize . f) xs)
mapCarrier _ t = t

instantiate :: [Expression] -> Expression -> Expression
instantiate args = mapExpression (\e -> case e of Input i | i >= 0 && i < length args -> Just (args !! i); _ -> Nothing)

-- Beta reduction for a field of a known construction; calls stay opaque.
normalize :: Expression -> Expression
normalize e = retain "native.normalization" e (normalizeStep e)

normalizeStep :: Expression -> Expression
normalizeStep (Project value f) = case normalize value of
  Construct s fields -> maybe (Project (Construct s fields) f) normalize (lookup f fields)
  value' -> Project value' f
normalizeStep (Construct s fields) = Construct s [(f,normalize v) | (f,v) <- fields]
normalizeStep (BoundCall s bindings args) = BoundCall s bindings (map normalize args)
normalizeStep (Call s args) = Call s (map normalize args)
normalizeStep (Equal x y) = Equal (normalize x) (normalize y)
normalizeStep (Numeric op x y) = case (op,normalize x,normalize y) of
  ("+",NumberLiteral a,NumberLiteral b) -> NumberLiteral (a+b)
  ("+",a,NumberLiteral 0) -> a
  ("+",NumberLiteral 0,b) -> b
  ("+",Numeric "+" a (NumberLiteral b),NumberLiteral c) -> Numeric "+" a (NumberLiteral (b+c))
  ("monus",Numeric "+" a (NumberLiteral b),NumberLiteral c) | b >= c -> normalizeStep (Numeric "+" a (NumberLiteral (b-c)))
  ("monus",NumberLiteral a,NumberLiteral b) -> NumberLiteral (max 0 (a-b))
  (_,a,b) -> Numeric op a b
normalizeStep (Sequence xs) = case concatMap flatten (map normalize xs) of
  [Project value field] | field == sequenceField -> Project value field
  [SequenceOp "tail" value] -> SequenceOp "tail" value
  values -> Sequence values
  where flatten (Sequence ys) = ys
        flatten x = [x]
normalizeStep (SequenceOp op xs) = case (op,normalize xs) of
  ("isEmpty",Sequence []) -> Literal True
  ("isEmpty",Sequence (_:_)) -> Literal False
  ("tail",Sequence (_:rest)) -> case rest of
    [Project value field] | field == sequenceField -> Project value field
    _ -> normalize (Sequence rest)
  (_,value) -> SequenceOp op value
normalizeStep (SequenceHead t xs) = case normalize xs of
  Sequence (x:_) -> x
  value -> SequenceHead t value
normalizeStep (Conditional p x y) = Conditional (normalize p) (normalize x) (normalize y)
normalizeStep e = e

-- Expansion uses independently checked helpers and certified finite normal
-- forms. A recursive symbol unfolds once per path; residual calls stay opaque.
-- Emission retains the original native calls and their checked dependency graph.
expand :: Helpers -> Expression -> Expression
expand helpers = go S.empty
  where
    go seen (Call s args) = case M.lookup s helpers of
      Just helper | S.notMember s seen -> go (S.insert s seen) (instantiate (map (go seen) args) (body helper))
      _ -> Call s (map (go seen) args)
    go seen (Project x f) = normalize (Project (go seen x) f)
    go seen (Construct s fs) = Construct s [(f,go seen x) | (f,x) <- fs]
    go seen (Sequence xs) = normalize (Sequence (map (go seen) xs))
    go seen (SequenceOp op xs) = normalize (SequenceOp op (go seen xs))
    go seen (SequenceHead t xs) = normalize (SequenceHead (mapCarrier (go seen) t) (go seen xs))
    go seen (Equal x y) = case (go seen x,go seen y) of
      (Literal a,Literal b) -> Literal (a == b)
      (Enumeration a x',Enumeration b y') -> Literal (a == b && x' == y')
      (x',y') | x' == y' -> Literal True
              | otherwise -> Equal x' y'
    go seen (Conditional p yes no) = case go seen p of
      Literal True -> go seen yes
      Literal False -> go seen no
      p' -> let yes' = go seen yes; no' = go seen no in
        if yes' == no' then yes' else Conditional p' yes' no'
    go _ e = e

recordFieldType :: Shape -> Expression -> Carrier -> Carrier
recordFieldType sh receiver = mapCarrier (instantiate [Project receiver f | c <- variants sh,(f,_) <- payload c])

familyCarrier :: Shape -> [Expression] -> Carrier
familyCarrier sh xs = if null (indexTypes sh) then Named (shapeSymbol sh) else Fibre (shapeSymbol sh) xs

indexField :: Text -> Int -> Text
indexField s i = s <> ".index" <> T.pack (show i)

-- A monotone admission pass resolves nested products/sums in dependency order.
-- Cycles are never provisionally accepted, so recursive carriers stay explicit.
discover :: Inventory -> M.Map Text F.Domain -> (Shapes,M.Map Text Refusal)
discover inv finite = go M.empty candidates
  where
    initialHelpers = finiteHelpers inv finite
    candidates = M.filterWithKey (\s d -> get "nativeFamily" d /= Null || (S.member (s,"structure") (required inv)
      && get "kind" d `elem` [String "record",String "datatype"]
      && not (get "kind" d == String "datatype" && S.member (s,"behavior") (required inv))
      && s /= builtin inv "bool" && s /= builtin inv "nat" && not (M.member s finite))) (declarations inv)
    header helpers accepted d = do
      unless (get "kind" d == String "datatype" && get "parameters" d == Number 0) (refuse Representation "No provisional datatype header")
      ty <- field inv "type" d
      (args,_,out) <- typedTelescope inv finite helpers accepted ty
      unless (get "tag" (get "term" out) == String "sort") (refuse Representation "Invalid datatype header")
      pure ((Shape (string (get "name" d)) False [] args) {typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d})
    deps sh = S.fromList [s | t <- indexTypes sh ++ case sequenceElement sh of
        Just element -> [element]
        Nothing -> [t | c <- variants sh,(_,t) <- payload c]
      ,s <- case t of Named s -> [s]; Fibre s _ -> [s]; _ -> []]
    close accepted table = let next = M.filter (\sh -> deps sh `S.isSubsetOf` (M.keysSet accepted `S.union` M.keysSet table `S.union` M.keysSet finite)) table
      in if M.keysSet next == M.keysSet table then table else close accepted next
    go accepted pending = let
      helpers = indexHelpers inv finite accepted initialHelpers
      headers = M.mapMaybe (either (const Nothing) Just . header helpers accepted) pending
      attempts = M.map (shape inv finite helpers (M.union accepted headers)) pending
      parsed = close accepted (M.mapMaybe (either (const Nothing) Just) attempts)
      components = stronglyConnComp [(sh,s,S.toList (deps sh)) | (s,sh) <- M.toList parsed]
      checked (AcyclicSCC sh) = Right [sh]
      checked (CyclicSCC shapes') = do
        unless (all (\sh -> not (isRecord sh) && sequenceElement sh == Nothing
          && maybe False (inductiveChecked inv) (M.lookup (shapeSymbol sh) (declarations inv))) shapes')
          (refuse Semantics "Recursive carrier component lacks safe inductive positivity evidence")
        let peers = map shapeSymbol shapes'
        pure [sh {recursivePeers = peers} | sh <- shapes']
      groups = map checked components
      members = close accepted (M.fromList [(shapeSymbol sh,sh) | Right group <- groups,sh <- group])
      admitted = M.union members (M.fromList [(shapeSymbol row,row) | sh <- M.elems members,Just _ <- [relationParameter sh],let row = relationRow sh])
      remaining = M.difference pending admitted
      failure _ (Left reason) = reason
      failure s (Right _) = case [reason | (CyclicSCC group,Left reason) <- zip components groups,any ((== s) . shapeSymbol) group] of
        reason:_ -> reason
        _ -> refusal Representation "Carrier depends on an unadmitted recursive component"
      in if M.null admitted then (accepted,M.mapWithKey failure attempts)
         else go (M.union accepted admitted) remaining

shape :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> Value -> Either Refusal Shape
shape inv finite helpers shapes d | get "nativeFamily" d /= Null = do
  slot <- integer (get "nativeFamily" d)
  domains <- traverse (carrierIn inv finite helpers shapes []) (array (get "familyDomains" d))
  let symbol = string (get "name" d)
      member = Shape symbol True [Constructor (symbol <> ".member") [(familyValue symbol,AnyValue)] []] domains
  pure (member {typeParameters = Specialize.nativeParameters d,familyParameters = [(slot,symbol)],relationParameter = Just slot})
shape inv finite helpers shapes d | get "nativeSequence" d /= Null = do
  element <- carrierIn inv finite helpers shapes [] (get "nativeSequence" d)
  cs <- map string . array <$> field inv "constructors" d
  let s = string (get "name" d)
      provisional = (Shape s False [] []) {sequenceElement = Just element,typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d}
  unless (length cs == 2) (refuse Syntax "Sequence constructor coverage mismatch")
  constructors <- forM (zip cs [[],[element,Named s]]) $ \(c,expected) -> do
    def <- maybe (refuse Syntax "Missing sequence constructor") Right (M.lookup c (declarations inv))
    cty <- field inv "type" def
    (types,env,res) <- typedTelescope inv finite helpers (M.insert s provisional shapes) cty
    out <- carrierIn inv finite helpers (M.insert s provisional shapes) env res
    unless (types == expected && out == Named s) (refuse Semantics "Sequence constructor signature mismatch")
    pure (Constructor c [(c <> ".payload" <> T.pack (show i),t) | (i,t) <- zip [0 :: Int ..] types] [])
  pure (provisional {variants = constructors})
shape inv finite helpers shapes d = do
  unless (get "abstract" d == Bool False) (refuse Representation "Abstract carrier has no exposed value representation")
  pars <- field inv "parameters" d >>= integer
  ty <- field inv "type" d
  (familyArgs,_,familyResult) <- typedTelescope inv finite helpers shapes ty
  unless (pars == 0 && get "tag" (get "term" familyResult) == String "sort")
    (refuse Representation "Family requires admitted indices and no unresolved parameters")
  let s = string (get "name" d); record = get "kind" d == String "record"
  unless (not record || null familyArgs || get "nativeRecordCaptures" d == toJSON (length familyArgs))
    (refuse Representation "Indexed record parameters require specialization")
  cs <- if record then do
    induction <- field inv "induction" d
    unless (induction `elem` [String "Nothing",String "Just Inductive"]) $
      refuse Representation "Coinductive records require a separate carrier rule"
    c <- string <$> field inv "constructor" d
    pure [c]
    else map string . array <$> field inv "constructors" d
  unless (not (null cs) && length cs == S.size (S.fromList cs)) $
    refuse Semantics "Algebraic carrier requires distinct, nonempty constructor coverage"
  constructors <- forM cs $ \c -> do
    def <- maybe (refuse Syntax "Missing checked constructor declaration") Right (M.lookup c (declarations inv))
    unless (get "kind" def == String "constructor") (refuse Syntax "Carrier refers to a non-constructor declaration")
    cty <- field inv "type" def
    (types,env,res) <- typedTelescope inv finite helpers shapes cty
    let resultTerm = get "term" res
    unless (get "tag" resultTerm == String "definition" && get "symbol" resultTerm == String s)
      (refuse Semantics "Constructor result does not match its family")
    endpoints <- traverse applicationValue (array (get "eliminations" resultTerm))
    unless (length endpoints == length familyArgs) (refuse Syntax "Constructor result index arity mismatch")
    indices <- foldM (\prior (domain,endpoint) -> do
      value <- indexExpression inv finite helpers shapes env (mapCarrier (instantiate prior) domain) endpoint
      pure (prior ++ [value])) [] (zip familyArgs endpoints)
    -- typedTelescope admits each payload in the preceding payload context.
    -- The same ordered dependency rule applies to records and sum variants;
    -- construction, branch expansion and guarded validity retain these links.
    names <- if record then map string . array <$> field inv "fields" d
      else pure [c <> ".payload" <> T.pack (show i) | i <- [0..length types-1]]
    unless (length names == length types && S.size (S.fromList names) == length names) $
      refuse Semantics "Record fields do not correspond one-to-one with its constructor telescope"
    let con = Constructor c (zip names types) indices
        candidate = Shape s record [con] familyArgs
    if record then mapM_ (checkProjection candidate) (zip names types) else pure ()
    pure con
  pure ((Shape s record constructors familyArgs) {typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d})
  where
    checkProjection candidate (f,ty) = do
      let s = shapeSymbol candidate
          provisional = M.insert s candidate shapes
      d' <- maybe (refuse Syntax "Missing checked record projection") Right (M.lookup f (declarations inv))
      projection <- field inv "projection" d'
      unless (get "kind" d' == String "function" && get "proper" projection == String s
        && get "index" projection == Number 1) (refuse Semantics "Record field is not the corresponding proper projection")
      fty <- field inv "type" d'
      (args,env,res) <- typedTelescope inv finite helpers provisional fty
      unless (args == [Named s]) (refuse Representation "Record projection has a dependent or parameterized input")
      actual <- carrierIn inv finite helpers provisional env res
      unless (mapCarrier (expand helpers) actual == mapCarrier (expand helpers) (recordFieldType candidate (Input 0) ty)) (refuse Semantics "Record projection type disagrees with constructor payload")

symbols :: Shapes -> S.Set Text
symbols shapes = S.fromList $ concat
  [[shapeSymbol s] ++ map constructorSymbol (variants s)
    ++ (if isRecord s then concatMap (map fst . payload) (variants s) else []) | s <- M.elems shapes]

constructorTable :: Shapes -> M.Map Text (Shape,Constructor)
constructorTable shapes = M.fromList [(constructorSymbol c,(s,c)) | s <- M.elems shapes,c <- variants s]

projectionTable :: Shapes -> M.Map Text (Text,Carrier)
projectionTable shapes = M.fromList [(f,(shapeSymbol s,recordFieldType s (Input 0) t))
  | s <- M.elems shapes,isRecord s,c <- variants s,(f,t) <- payload c]

projectedCarrier :: Shapes -> Carrier -> Expression -> Carrier -> Carrier
projectedCarrier shapes receiver value fieldType = refine (mapCarrier (instantiate [value]) fieldType)
  where
    refine = case receiver of
      Fibre owner indices | Just sh <- M.lookup owner shapes,isRecord sh,[con] <- variants sh
        ,resultIndices con == map Input [0..length indices-1] ->
          let replacements = zip [Project value f | (f,_) <- take (length indices) (payload con)] indices
          in mapCarrier (foldl (\replace (left,right) -> mapExpression (\e -> if e == left then Just right else Nothing) . replace) id replacements)
      _ -> id

recordOwner :: Carrier -> Text -> Bool
recordOwner (Named actual) expected = actual == expected
recordOwner (Fibre actual _) expected = actual == expected
recordOwner _ _ = False

function :: Inventory -> M.Map Text F.Domain -> Shapes -> Value -> Either Refusal Calculation
function inv finite shapes = functionWith inv finite (indexHelpers inv finite shapes (finiteHelpers inv finite)) shapes M.empty

type Signatures = M.Map Text ([Carrier],Carrier)

signature :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> Value -> Either Refusal ([Carrier],Carrier)
signature inv finite helpers shapes d = do
  ty <- field inv "type" d
  (args,env,res) <- typedTelescope inv finite helpers shapes ty
  (args,) <$> carrierIn inv finite helpers shapes env res

-- Check bodies as well as signatures, then close over actual invocation nodes.
-- A failed/recursive helper prevents every caller from acquiring a native rule.
functions :: Inventory -> M.Map Text F.Domain -> Shapes -> M.Map Text (Either Refusal Calculation)
functions inv finite shapes = functionsWith (indexHelpers inv finite shapes (finiteHelpers inv finite)) inv finite shapes

-- Finite-only signatures do not depend on family admission. Validate their
-- bodies and acyclic dependency closure before exposing them to index parsing.
finiteHelpers :: Inventory -> M.Map Text F.Domain -> Helpers
finiteHelpers inv finite = close acyclic
  where
    admitted = M.filter (null . staticIndexEquations) $ M.mapMaybe (either (const Nothing) Just) (functionsWith M.empty inv finite M.empty)
    acyclic = M.fromList [(calculationSymbol c,c) | AcyclicSCC c <- stronglyConnComp
      [(c,s,S.toList (dependencies c)) | (s,c) <- M.toList admitted]]
    close table = let next = M.filter (\c -> dependencies c `S.isSubsetOf` M.keysSet table) table
      in if M.keysSet next == M.keysSet table then table else close next

-- Index helpers use already admitted carriers, independently of families that
-- consume their results. Indexed recursive results require checked termination;
-- unindexed recursion still needs the structural concatenation certificate.
-- Recursive concatenation has a checked structural equation certificate; its
-- finite comparison normal form is separate from the emitted recursive body.
indexHelpers :: Inventory -> M.Map Text F.Domain -> Shapes -> Helpers -> Helpers
indexHelpers inv finite shapes initial = close candidates
  where
    admitted = M.filter (null . staticIndexEquations) $ M.mapMaybe (either (const Nothing) Just) (functionsWith initial inv finite shapes)
    groups = stronglyConnComp [(c,s,S.toList (dependencies c)) | (s,c) <- M.toList admitted]
    candidates = M.union initial (M.fromList (concatMap select groups))
    select (AcyclicSCC c) = [(calculationSymbol c,c)]
    select (CyclicSCC [c]) = case concatenationNormalForm shapes c of
      Just expression -> [(calculationSymbol c,c {body = Annotated
        (D.derived "native.schema-concatenation" [D.root (calculationSymbol c) "compiled",D.root (calculationSymbol c) "type"]
          Null [annotation (body c)]) expression})]
      Nothing | checked [c] -> [(calculationSymbol c,c)]
              | otherwise -> []
    select (CyclicSCC cs) | checked cs = [(calculationSymbol c,c) | c <- cs]
                        | otherwise = []
    checked = all (\c -> case result c of
      Fibre{} -> maybe False (terminationChecked inv) (M.lookup (calculationSymbol c) (declarations inv))
      _ -> False)
    close table = let next = M.filter (\c -> dependencies c `S.isSubsetOf` M.keysSet table) table
      in if M.keysSet next == M.keysSet table then table else close next

concatenationNormalForm :: Shapes -> Calculation -> Maybe Expression
concatenationNormalForm shapes calc = case (inputs calc,result calc) of
  ([Named first,Named second],Named output) | first == second && second == output -> do
    sh <- M.lookup output shapes
    element <- sequenceElement sh
    let xs = Input 0; ys = Input 1
        items = Project xs sequenceField
        tailValue = Construct output [(sequenceField,SequenceOp "tail" items)]
        recursive = Call (calculationSymbol calc) [tailValue,ys]
        step = Construct output [(sequenceField,Sequence [SequenceHead element items,Project recursive sequenceField])]
        expected = Conditional (Equal (SequenceOp "isEmpty" items) (Literal True)) ys step
    if normalize (body calc) == normalize expected
      then Just (Construct output [(sequenceField,Sequence [Project xs sequenceField,Project ys sequenceField])])
      else Nothing
  _ -> Nothing

functionsWith :: Helpers -> Inventory -> M.Map Text F.Domain -> Shapes -> M.Map Text (Either Refusal Calculation)
functionsWith helpers inv finite shapes = close checkedCycles
  where
    candidates = M.filterWithKey (\s d -> S.member (s,"behavior") (required inv)
      && get "kind" d `elem` [String "function",String "primitive"]) (declarations inv)
    signatures = M.mapMaybe (either (const Nothing) Just . signature inv finite helpers shapes) candidates
    lowered = M.map (functionWith inv finite helpers shapes signatures) candidates
    cycles = [cs | CyclicSCC cs <- stronglyConnComp
      [(s,s,S.toList (dependencies c)) | (s,Right c) <- M.toList lowered]]
    unsupportedCycles = S.fromList (concat [cs | cs <- cycles,
      not (all (\s -> maybe False (terminationChecked inv) (M.lookup s candidates)) cs)])
    checkedCycles = M.mapWithKey (\s result' -> if S.member s unsupportedCycles
      then refuse Semantics "Recursive native call cycle lacks checked safe-module termination" else result') lowered
    close table =
      let next = M.map checkDependencies table
          accepted = M.keysSet . M.filter (either (const False) (const True))
      in if accepted next == accepted table then next else close next
      where
        checkDependencies failure@Left{} = failure
        checkDependencies (Right calc) = do
          forM (S.toAscList (dependencies calc)) (\callee -> case M.lookup callee table of
            Nothing -> refuse Semantics ("Callee is outside the checked behavioral closure: " <> callee)
            Just (Left reason) -> Left (context ("Unsupported callee " <> callee <> ": ") reason)
            Just (Right _) -> Right ()) >> Right calc

dependencies :: Calculation -> S.Set Text
dependencies calc = calls (body calc) `S.union` S.unions
  [S.unions (map calls xs) | Fibre _ xs <- result calc : inputs calc]
  `S.union` S.unions [calls left `S.union` calls right | (_,left,right) <- staticIndexEquations calc]

calls :: Expression -> S.Set Text
calls (Call s args) = S.insert s (S.unions (map calls args))
calls (Construct _ fields) = S.unions (map (calls . snd) fields)
calls (Project x _) = calls x
calls (Equal x y) = calls x `S.union` calls y
calls (Numeric _ x y) = calls x `S.union` calls y
calls (Sequence xs) = S.unions (map calls xs)
calls (SequenceOp _ xs) = calls xs
calls (SequenceHead _ xs) = calls xs
calls (Conditional p yes no) = S.unions (map calls [p,yes,no])
calls _ = S.empty

functionWith :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> Signatures -> Value -> Either Refusal Calculation
functionWith inv finite helpers shapes signatures d = do
  unless (get "abstract" d /= Bool True && get "opaque" d /= Bool True)
    (refuse Semantics "Opaque helper body cannot justify a native calculation")
  let s = string (get "name" d)
  (ins,out) <- signature inv finite helpers shapes d
  equations <- forM (array (get "closureIndexEquations" d)) $ \equation -> do
    let env = reverse (zip ins (map Input [0..]))
    domain <- carrierIn inv finite helpers shapes env (get "domain" equation)
    left <- indexExpression inv finite helpers shapes env domain (get "left" equation)
    right <- indexExpression inv finite helpers shapes env domain (get "right" equation)
    pure (domain,left,right)
  lowered <- if get "kind" d == String "primitive" then do
    let operation = primitiveOperation (string (get "primitive" d))
    (op,typ) <- maybe (refuse Semantics "Primitive has no native arithmetic rule") Right operation
    unless (ins == [Natural,Natural] && out == typ) (refuse Semantics "Primitive arithmetic signature mismatch")
    ty <- field inv "type" d
    pure (located "native.natural-primitive" ty (get "primitive" d) (Numeric op (Input 0) (Input 1)))
    else case M.lookup s projections of
    Just (owner,typ) -> do
      unless (ins == [Named owner] && out == typ) (refuse Syntax "Proper projection signature mismatch")
      pure (Project (Input 0) s)
    Nothing -> do
      unless (length (array (get "sourceSyntax" d)) == 1
        || (get "withParent" d /= Null && M.member (string (get "withParent" d)) (declarations inv))
        || get "extendedLambda" d == Bool True)
        (refuse Syntax "No uniquely anchored source definition or checked generated helper")
      tree <- field inv "compiled" d
      p <- field inv "projection" d
      dropped <- if p == Null then Right 0 else subtract 1 <$> integer (get "index" p)
      unless (dropped >= 0 && dropped <= length ins)
        (refuse Representation "Unsupported omitted runtime indices")
      lower Nothing [(left,right) | (_,left,right) <- equations] out (drop dropped (zip ins (map Input [0..]))) tree
  pure (Calculation s ins out lowered equations)
  where
    constructors = constructorTable shapes
    projections = projectionTable shapes
    rewrite equations = foldl (\f (left,right) -> mapExpression (\x -> if x == left then Just right else Nothing) . f) id equations
    requireType equations expected (actual,expr) = if canonical actual == canonical expected
      then Right expr else refuse Semantics ("Expression carrier mismatch: expected " <> describe (canonical expected)
        <> "; actual " <> describe (canonical actual))
      where canonical (Fibre family indices) = case M.lookup family shapes of
              Just sh -> Fibre family [canonicalIndex domain index | (domain,index) <- zip (indexTypes sh) indices]
              Nothing -> mapCarrier (expand helpers . rewrite equations) (Fibre family indices)
            canonical typ = typ
            canonicalIndex domain value = let expanded = expand helpers (rewrite equations value) in case domain of
              Named owner | Just sh <- M.lookup owner shapes, Just _ <- sequenceElement sh ->
                normalize (Project expanded sequenceField)
              _ -> normalize expanded
            describe (Fibre s xs) = s <> "[" <> T.intercalate "," (map (renderWith id (T.pack . show)) xs) <> "]"
            describe t = T.pack (show t)
    lower inherited equationsInScope out env tree = fmap (located "native.algebraic-case" tree
      (object ["bindings" .= [renderWith id (T.pack . show) x | (_,x) <- env]
        ,"equations" .= [(renderWith id (T.pack . show) a,renderWith id (T.pack . show) b) | (a,b) <- equationsInScope]])) $ case string (get "tag" tree) of
      "absurd" -> do
        unless (length (array (get "binders" tree)) == length env) (refuse Syntax "Absurd leaf binder count mismatch")
        let impossible = any (\(typ,value) -> case alternatives equationsInScope (mapCarrier (rewrite equationsInScope) typ) value of
              Right [] -> True
              _ -> False) env
        unless impossible (refuse Semantics "Absurd branch has no established empty index fibre")
        pure Absent
      "done" -> do
        unless (length (array (get "binders" tree)) == length env) (refuse Syntax "Case leaf binder count mismatch")
        expressionExpected (Just out) equationsInScope (reverse env) (get "body" tree) >>= requireType equationsInScope out
      "case" | get "copattern" tree == Bool True -> do
        i <- integer (get "value" (get "argument" tree))
        unless (i == length env && get "catchall" tree == Null && get "eta" tree == Null
          && null (array (get "literals" tree))) (refuse Syntax "Malformed record copattern split")
        owner <- case out of Named owner -> Right owner; _ -> refuse Representation "Copattern result is not a plain record"
        sh <- maybe (refuse Representation "Copattern result record missing") Right (M.lookup owner shapes)
        con <- case variants sh of [con] | isRecord sh -> Right con; _ -> refuse Semantics "Copattern result is not a record"
        let branches = array (get "constructors" tree)
        unless (length branches == length (payload con) && all (\(f,_) -> length (filter ((== String f) . get "symbol") branches) == 1) (payload con))
          (refuse Semantics "Copattern fields do not cover the result record")
        values <- forM (payload con) $ \(f,ty) -> do
          b <- case filter ((== String f) . get "symbol") branches of [b] -> Right (get "branch" b); _ -> refuse Syntax "Missing record copattern"
          unless (get "arity" b == Number 0) (refuse Syntax "Projection pattern has constructor payloads")
          (f,) <$> lower Nothing equationsInScope ty env (get "tree" b)
        pure (Construct owner values)
      "case" -> do
        unless (get "copattern" tree == Bool False && null (array (get "literals" tree))
          && get "fallThrough" tree == Bool False) $
          refuse Semantics "Case tree requires additional matching semantics"
        i <- integer (get "value" (get "argument" tree))
        (typ,rawSelected) <- at i env
        let selected = located "native.algebraic-discriminant" tree (toJSON i) rawSelected
        options <- alternatives equationsInScope typ selected
        let eta = get "eta" tree
            ordinary = array (get "constructors" tree)
            available = if eta == Null then ordinary else
              [object ["symbol" .= get "constructor" eta,"branch" .= get "branch" eta]]
            recordShape = case typ of
              Named owner -> maybe False isRecord (M.lookup owner shapes)
              Fibre owner _ -> maybe False isRecord (M.lookup owner shapes)
              _ -> False
        unless (get "lazy" tree == Bool False || recordShape || length options <= 1)
          (refuse Semantics "Lazy matching requires a uniquely determined constructor")
        unless (eta == Null || (recordShape && null ordinary)) (refuse Semantics "Eta branch is not a unique record split")
        let names = map (string . get "symbol") available
        unless (length names == S.size (S.fromList names)
          && S.fromList names `S.isSubsetOf` S.fromList (map fst options)
          && (get "catchall" tree /= Null || inherited /= Nothing || length names == length options)) $
          refuse Semantics "Constructor branches are not exhaustive and distinct"
        let fallback = if get "catchall" tree == Null then inherited
              else Just (lower inherited equationsInScope out env (get "catchall" tree))
        branches <- forM options $ \(c,allFields) -> case filter ((== String c) . get "symbol") available of
         [] | Just fallbackBody <- fallback -> (c,) <$> fallbackBody
         [branch] -> do
          parameterCount <- runtimeParameters c
          let captureCount = maybe 0 (\d -> case get "patternCaptures" d of Number n -> round n; _ -> 0) (M.lookup c (declarations inv))
              fields = drop (parameterCount+captureCount) allFields
          let b = get "branch" branch
          arity <- integer (get "arity" b)
          unless (arity == length fields) (refuse Syntax "Case branch arity does not preserve every constructor payload")
          whenEta eta fields
          let project f = located "native.case-payload" tree
                (object ["constructor" .= c,"field" .= f,"argument" .= i])
                (case typ of
                  Natural -> Numeric "monus" selected (NumberLiteral 1)
                  Named owner | Just sh <- M.lookup owner shapes, Just element <- sequenceElement sh ->
                    if any ((== f) . fst) (take 1 fields) then SequenceHead element (Project selected sequenceField)
                    else Construct owner [(sequenceField,SequenceOp "tail" (Project selected sequenceField))]
                  _ -> Project selected f)
              fieldValues = [project f | (f,_) <- allFields]
              expanded = take i env ++ [(mapCarrier (instantiate fieldValues) t,project f) | (f,t) <- fields] ++ drop (i+1) env
          equations <- branchEquations typ selected c
          let refined = [(mapCarrier (rewrite equations) t,rewrite equations value) | (t,value) <- expanded]
              inheritedEquations = [(rewrite equations left,rewrite equations right) | (left,right) <- equationsInScope]
          e <- lower fallback (inheritedEquations ++ equations) (mapCarrier (rewrite equations) out) refined (get "tree" b)
          pure (c,e)
         _ -> refuse Syntax "Constructor branch identity mismatch"
        choose tree typ selected branches
      _ -> refuse Syntax "Body is outside the finite algebraic case rule"
    whenEta eta fields = unless (eta == Null || map string (array (get "fields" eta)) == map fst fields) $
      refuse Syntax "Eta branch fields disagree with checked record field order"
    runtimeParameters c = case M.lookup c (declarations inv) of
      Just def | get "runtimeParameters" def /= Null -> integer (get "runtimeParameters" def)
      _ -> Right 0
    alternatives _ Boolean _ = Right [(builtin inv "true",[]),(builtin inv "false",[])]
    alternatives _ Natural value = let
      options = [(builtin inv "zero",[]),(builtin inv "suc",[("predecessor",Natural)])]
      in Right $ case normalize value of
        NumberLiteral 0 -> take 1 options
        NumberLiteral k | k > 0 -> drop 1 options
        Numeric "+" _ (NumberLiteral k) | k > 0 -> drop 1 options
        _ -> options
    alternatives _ TypeParameter{} _ = refuse Semantics "Cannot inspect constructors of an open type parameter"
    alternatives _ AnyValue _ = refuse Semantics "Cannot inspect a native relation payload"
    alternatives equations (Fibre s indices) selected = do
      sh <- maybe (refuse Representation "Missing indexed carrier") Right (M.lookup s shapes)
      pure [(constructorSymbol c,payload c) | c <- variants sh,compatible equations (indexTypes sh) indices (endpoints selected c)]
    alternatives _ (Named s) selected = case M.lookup s shapes of
      Just sh -> let options = [(constructorSymbol c,payload c) | c <- variants sh]
        in Right $ case (sequenceElement sh,normalize (Project selected sequenceField)) of
          (Just _,Sequence []) -> take 1 options
          (Just _,Sequence (_:_)) -> drop 1 options
          _ -> options
      Nothing -> maybe (refuse Representation "Missing case carrier") (Right . map (,[]) . F.constructors) (M.lookup s finite)
    endpoints selected c = map (instantiate [Project selected f | (f,_) <- payload c]) (resultIndices c)
    distinct (Literal a) (Literal b) = a /= b
    distinct (Enumeration a x) (Enumeration b y) = a /= b || x /= y
    distinct (NumberLiteral a) (NumberLiteral b) = a /= b
    distinct (NumberLiteral 0) (Numeric "+" _ (NumberLiteral k)) = k > 0
    distinct (Numeric "+" _ (NumberLiteral k)) (NumberLiteral 0) = k > 0
    distinct (Construct s [(f,Sequence xs)]) (Construct t [(g,Sequence ys)])
      | s == t && f == sequenceField && g == sequenceField = null xs /= null ys
    distinct _ _ = False
    compatible equations domains xs ys = length xs == length ys && length domains == length xs
      && not (or (zipWith3 (separated S.empty) domains xs ys))
      where
        reduced = normalize . expand helpers . rewrite equations
        separated seen domain x y = distinct (reduced x) (reduced y) || case ownerOf domain >>= (`M.lookup` shapes) of
          Just sh | sequenceElement sh == Nothing, S.notMember (shapeSymbol sh) seen ->
            let leftTag = reduced (Project x tagField)
                rightTag = reduced (Project y tagField)
                active con = isRecord sh || case (leftTag,rightTag) of
                  (Enumeration _ a,Enumeration _ b) -> a == b && a == constructorSymbol con
                  _ -> False
                payloadSeparated con = any (\(f,typ) -> separated (S.insert (shapeSymbol sh) seen)
                  (mapCarrier (instantiate [Project x field | (field,_) <- payload con]) typ)
                  (Project x f) (Project y f)) (payload con)
            in (not (isRecord sh) && distinct leftTag rightTag)
              || any payloadSeparated (filter active (variants sh))
          _ -> False
        ownerOf (Named owner) = Just owner
        ownerOf (Fibre owner _) = Just owner
        ownerOf _ = Nothing
    branchEquations (Fibre s xs) selected c = do
      sh <- maybe (refuse Representation "Missing family") Right (M.lookup s shapes)
      con <- case filter ((== c) . constructorSymbol) (variants sh) of
        [v] -> Right v
        _ -> refuse Representation "Missing family branch"
      -- Only replace symbolic references. Constants are never rewritten.
      let tagFact = [(Project selected tagField,Enumeration (tagType s) c)
            | not (isRecord sh),sequenceElement sh == Nothing]
      pure (tagFact ++ concatMap orient (zip xs (endpoints selected con)))
      where
        orient (Numeric "+" x (NumberLiteral a),Numeric "+" y (NumberLiteral b)) | a == b = orient (x,y)
        orient (NumberLiteral a,Numeric "+" y (NumberLiteral b)) | a >= b = orient (NumberLiteral (a-b),y)
        orient (Numeric "+" x (NumberLiteral a),NumberLiteral b) | b >= a = orient (x,NumberLiteral (b-a))
        orient (Construct s [(f,x)],Construct t [(g,y)])
          | s == t && f == sequenceField && g == sequenceField = orientSequence s (x,y)
        orient (Sequence (x:xs),Sequence (y:ys)) = orient (x,y) ++ orient (Sequence xs,Sequence ys)
        orient (x,y) | x == y = []
                     | isReference x = [(x,y)]
                     | isReference y = [(y,x)]
                     | otherwise = []
        orientSequence _ (Sequence [x,Project xs f],Sequence [y,Project ys g])
          | f == sequenceField && g == sequenceField = orient (x,y) ++ orient (xs,ys)
        orientSequence owner (Sequence (x:xs),Sequence [y,Project ys f])
          | f == sequenceField = orient (x,y) ++ orient (Construct owner [(sequenceField,Sequence xs)],ys)
        orientSequence owner (Sequence [x,Project xs f],Sequence (y:ys))
          | f == sequenceField = orient (x,y) ++ orient (xs,Construct owner [(sequenceField,Sequence ys)])
        orientSequence _ values = orient values
    branchEquations Boolean selected c = Right [(selected,Literal (c == builtin inv "true"))]
    branchEquations Natural selected c | c == builtin inv "zero" = Right [(selected,NumberLiteral 0)]
    branchEquations Natural selected c | c == builtin inv "suc" =
      Right [(Numeric "+" (Numeric "monus" selected (NumberLiteral 1)) (NumberLiteral 1),selected)]
    branchEquations (Named s) selected c | M.member s finite = Right [(selected,Enumeration s c)]
    branchEquations (Named s) selected c | Just sh <- M.lookup s shapes, Just element <- sequenceElement sh =
      Right $ case variants sh of
       [nil,cons] | c == constructorSymbol nil -> [(selected,Construct s [(sequenceField,Sequence [])])]
                 | c == constructorSymbol cons ->
        [(selected,Construct s [(sequenceField,Sequence [SequenceHead element (Project selected sequenceField)
          ,SequenceOp "tail" (Project selected sequenceField)])])]
       _ -> case normalize (Project selected sequenceField) of
        Sequence [_,Project tailValue field] | field == sequenceField ->
          [(Construct s [(sequenceField,Project tailValue sequenceField)],tailValue)]
        _ -> []
    branchEquations (Named s) selected c | Just sh <- M.lookup s shapes, not (isRecord sh) =
      Right [(Project selected tagField,Enumeration (tagType s) c)]
    branchEquations _ _ _ = Right []
    isReference Input{} = True
    isReference Project{} = True
    isReference (Call s _) = M.member s helpers
    isReference _ = False
    choose _ Fibre{} _ [] = Right Absent
    choose _ _ _ [] = refuse Semantics "Empty case coverage"
    choose _ _ _ [(_,e)] = Right e
    choose tree typ selected ((c,e):rest) = do
      condition <- test tree typ selected c
      fallback <- choose tree typ selected rest
      pure (located "native.algebraic-choice" tree (object ["constructor" .= c]) (Conditional condition e fallback))
    test tree typ selected c = let
      mark = located "native.algebraic-test" tree (object ["constructor" .= c])
      in fmap mark $ case typ of
        Boolean -> Right (Equal selected (mark (Literal (c == builtin inv "true"))))
        Natural -> if c == builtin inv "zero" then Right (Equal selected (mark (NumberLiteral 0)))
          else Right (Numeric "<" (mark (NumberLiteral 0)) selected)
        TypeParameter{} -> refuse Semantics "Cannot test constructors of an open type parameter"
        AnyValue -> refuse Semantics "Cannot test constructors of a native relation payload"
        Fibre s _ -> test tree (Named s) selected c
        Named s -> case M.lookup s shapes of
          Just sh | Just _ <- sequenceElement sh -> Right (Equal (SequenceOp "isEmpty" (Project selected sequenceField))
            (Literal (any ((== c) . constructorSymbol) (take 1 (variants sh)))))
          Just sh | not (isRecord sh) -> Right (Equal (mark (Project selected tagField)) (mark (Enumeration (tagType s) c)))
          _ -> Right (Equal selected (mark (Enumeration s c)))
    expression = expressionExpected Nothing
    expressionExpected expected equationsInScope env term = fmap (\(typ,e) -> (typ,located "native.algebraic-term" term
      (object ["bindings" .= [renderWith id (T.pack . show) x | (_,x) <- env]
        ,"equations" .= [(renderWith id (T.pack . show) a,renderWith id (T.pack . show) b) | (a,b) <- equationsInScope]]) e)) $ do
      let es = array (get "eliminations" term)
      case string (get "tag" term) of
        "literal" | get "tag" (get "literal" term) == String "natural" -> do
          n <- case get "value" (get "literal" term) of
            Number v -> case floatingOrInteger v :: Either Double Integer of
              Right n | n >= 0 -> Right n
              _ -> refuse Syntax "Invalid natural literal"
            _ -> refuse Syntax "Missing natural literal"
          eliminate (Natural,NumberLiteral n) es
        "variable" -> do
          i <- integer (get "index" term)
          start <- at i env
          eliminate start es
        "constructor" -> do
          let c = string (get "symbol" term)
          case M.lookup c constructors of
            Just (sh,con) -> do
              parameterCount <- runtimeParameters c
              prefix <- if parameterCount == 0 then pure [] else case expected of
                Just (Fibre owner indices) | owner == shapeSymbol sh && length indices >= parameterCount -> pure (take parameterCount indices)
                _ -> refuse Representation "Constructor needs its contextual value parameters"
              let suppliedTypes = drop parameterCount (map snd (payload con))
                  (apps,rest) = splitAt (length suppliedTypes) es
              unless (length apps == length suppliedTypes) (refuse Representation "Partially applied payload constructor")
              values <- foldM (\prior (typ,arg) -> do
                value <- argument equationsInScope env (mapCarrier (instantiate prior) typ) arg
                pure (prior ++ [value])) prefix (zip suppliedTypes apps)
              let indices = map (instantiate values) (resultIndices con)
              eliminate (familyCarrier sh indices,Construct (shapeSymbol sh) (construction (Just term) sh con values)) rest
            Nothing | c == builtin inv "true" -> eliminate (Boolean,Literal True) es
                    | c == builtin inv "false" -> eliminate (Boolean,Literal False) es
                    | c == builtin inv "zero" -> eliminate (Natural,NumberLiteral 0) es
                    | c == builtin inv "suc" -> case es of
                        a:rest -> do
                          value <- argument equationsInScope env Natural a
                          eliminate (Natural,Numeric "+" value (NumberLiteral 1)) rest
                        _ -> refuse Representation "Partially applied natural successor"
                    | otherwise -> case [F.domainSymbol dom | dom <- M.elems finite,c `elem` F.constructors dom] of
                        [s] -> eliminate (Named s,Enumeration s c) es
                        _ -> refuse Representation "Constructor has no admitted carrier"
        "definition" -> case M.lookup (string (get "symbol" term)) projections of
          Just (owner,typ) -> case es of
            a:rest -> do
              value <- argument equationsInScope env (Named owner) a
              eliminate (mapCarrier (instantiate [value]) typ,Project value (string (get "symbol" term))) rest
            _ -> refuse Representation "Partially applied record projection"
          Nothing -> do
            let callee = string (get "symbol" term)
            (ins,out) <- maybe (refuse Representation ("Callee has no admitted first-order signature: " <> callee)) Right (M.lookup callee signatures)
            cd <- maybe (refuse Syntax "Missing helper declaration") Right (M.lookup callee (declarations inv))
            p <- field inv "projection" cd
            dropped <- if p == Null then Right 0 else subtract 1 <$> integer (get "index" p)
            unless (dropped >= 0 && dropped <= length ins)
              (refuse Representation "Unsupported omitted helper indices")
            let (apps,rest) = splitAt (length ins - dropped) es
            unless (length apps == length ins - dropped) (refuse Representation ("Partially applied helper: " <> callee))
            actuals <- foldM (\prior (typ,e) -> do
              let contextType = mapCarrier (instantiate (map snd prior)) typ
              value <- applicationValue e >>= expressionExpected (if dropped == 0 then Just contextType else Nothing) equationsInScope env
              pure (prior ++ [value])) [] (zip (drop dropped ins) apps)
            -- Recover omitted finite inputs from the actual principal fibre.
            known <- foldM (recover equationsInScope) M.empty (zip (drop dropped ins) (map fst actuals))
            prefix <- traverse (\i -> maybe (refuse Semantics "Cannot recover omitted finite index") Right (M.lookup i known)) [0..dropped-1]
            let args = prefix ++ map snd actuals
                supplied = zip (drop dropped ins) actuals
            mapM_ (\(expected,value) -> () <$ requireType equationsInScope (mapCarrier (instantiate args) expected) value) supplied
            eliminate (mapCarrier (instantiate args) out,Call callee args) rest
        _ -> refuse Syntax "Term requires a rule beyond algebraic construction and projection"
    recover equations known (Fibre s xs,Fibre t ys) | s == t && length xs == length ys
      ,Just sh <- M.lookup s shapes = foldM bind known (zip3 (indexTypes sh) xs ys)
      where
        bind table (domain,Input i,y) = case M.lookup i table of
          Nothing -> Right (M.insert i y table)
          Just x | canonical domain x == canonical domain y -> Right table
          _ -> refuse Semantics "Inconsistent omitted index"
        bind table _ = Right table
        canonical domain value = let expanded = expand helpers (normalize (rewrite equations value)) in case domain of
          Named owner | Just sh <- M.lookup owner shapes, Just _ <- sequenceElement sh -> normalize (Project expanded sequenceField)
          _ -> normalize expanded
    recover _ known _ = Right known
    argument equationsInScope env typ a = do
      unless (get "tag" a == String "apply") (refuse Syntax "Constructor argument is not an application")
      expressionExpected (Just typ) equationsInScope env (get "value" (get "argument" a)) >>= requireType equationsInScope typ
    eliminate value [] = Right value
    eliminate (typ,expr) (e:es) = do
      unless (get "tag" e == String "project") (refuse Syntax "Unsupported value elimination")
      let f = string (get "symbol" e)
      (owner,ft) <- maybe (refuse Representation "Projection has no admitted record") Right (M.lookup f projections)
      unless (recordOwner typ owner) (refuse Semantics "Projection is applied to the wrong record")
      eliminate (projectedCarrier shapes typ expr ft,located "native.projection-elimination" e Null (Project expr f)) es

construction :: Maybe Value -> Shape -> Constructor -> [Expression] -> [(Text,Expression)]
construction _ sh _ values | Just _ <- sequenceElement sh = [(sequenceField,case values of
  [] -> Sequence []
  [x,xs] -> Sequence [x,Project xs sequenceField]
  _ -> error "admitted sequence constructor lost its payload arity")]
construction callSite sh con values =
  let supplied = zip (map fst (payload con)) values
      indices = zipWith (\i e -> (indexField (shapeSymbol sh) i,instantiate values e)) [0..] (resultIndices con)
      -- Discovery verified the canonical family result and ordered telescope
      -- for each constructor. These schema roots justify the generated value;
      -- a call site is additional evidence, never a replacement for the schema.
      schemaOrigin rule owners extra = D.derived rule
        [D.root c "type" | c <- owners]
        (object (["family" .= shapeSymbol sh,"selectedConstructor" .= constructorSymbol con] ++ extra))
        [D.origin "native.constructor-application" term Null [] | Just term <- [callSite]]
      tag = Annotated (schemaOrigin "native.constructor-tag" [constructorSymbol con] [])
        (Enumeration (tagType (shapeSymbol sh)) (constructorSymbol con))
      missing v i f = Annotated (schemaOrigin "native.inactive-payload"
        [constructorSymbol con,constructorSymbol v]
        ["slotConstructor" .= constructorSymbol v,"position" .= i,"field" .= f]) Absent
      measure = [(countField (shapeSymbol sh),foldl (Numeric "+") (NumberLiteral 1)
        [Project value (countField owner) | ((_,typ),value) <- zip (payload con) values
        ,owner <- recursiveOwner sh typ]) | not (null (recursivePeers sh))]
  in if isRecord sh then indices ++ supplied else
    (tagField,tag) : indices ++ measure ++ [(f,maybe (missing v i f) id (lookup f supplied))
      | v <- variants sh,(i,(f,_)) <- zip [0 :: Int ..] (payload v)]

quote :: Text -> Text
quote x = "'" <> T.replace "'" "\\'" (T.replace "\\" "\\\\" x) <> "'"

countField :: Text -> Text
countField s = s <> ".node-count"
recursiveOwner :: Shape -> Carrier -> [Text]
recursiveOwner sh typ = [s | s <- case typ of Named s -> [s]; Fibre s _ -> [s]; _ -> [],s `elem` recursivePeers sh]

sequenceField :: Text
sequenceField = "items"

-- Generated names live inside each carrier or are derived from its canonical
-- identity and resolved by Target alongside every other emitted symbol.
tagType :: Text -> Text
tagType s = s <> ".constructor-tag"

tagField :: Text
tagField = "constructor"

validitySymbol :: Text -> Text
validitySymbol s = s <> ".payload-valid"

renderCarrier :: (Text -> Text) -> Carrier -> Text
renderCarrier _ Boolean = "ScalarValues::Boolean"
renderCarrier _ Natural = "ScalarValues::Natural"
renderCarrier _ TypeParameter{} = "Base::Anything"
renderCarrier _ AnyValue = "Base::Anything"
renderCarrier label (Named s) = quote (label s)
renderCarrier label (Fibre s _) = quote (label s)

renderWith :: (Text -> Text) -> (Int -> Text) -> Expression -> Text
renderWith label input = D.render . renderWithDoc label input ""

renderWithDoc :: (Text -> Text) -> (Int -> Text) -> Text -> Expression -> D.Doc
renderWithDoc label input owner = renderParameterizedDoc label input owner (const []) (const []) quote

parameterName :: Int -> Text
parameterName i = "typeArgument" <> T.pack (show i)

familyName :: Int -> Text
familyName i = "familyArgument" <> T.pack (show i)
familyRow :: Text -> Text
familyRow s = s <> ".relation-row"
familyValue :: Text -> Text
familyValue s = s <> ".value"
relationRow :: Shape -> Shape
relationRow member = Shape s True [Constructor (s <> ".row") fields []] []
  where
    s = familyRow (shapeSymbol member)
    unbound TypeParameter{} = AnyValue
    unbound t = t
    fields = [(indexField s i,unbound t) | (i,t) <- zip [0..] (indexTypes member)] ++ [(familyValue s,AnyValue)]

renderParameterizedDoc :: (Text -> Text) -> (Int -> Text) -> Text -> (Text -> [Text]) -> (Text -> [Text]) -> (Text -> Text) -> Expression -> D.Doc
renderParameterizedDoc label input owner calcParameters shapeParameters parameter = go
  where
    go e = D.mark owner (role e) (evidence e) $ case e of
      Input i -> D.text (input i)
      Literal b -> if b then "true" else "false"
      NumberLiteral n -> D.text (naturalText n)
      Numeric "monus" x y -> "(if " <> go x <> " < " <> go y <> " ? 0 else " <> go x <> " - " <> go y <> ")"
      Numeric op x y -> "(" <> go x <> D.text (" " <> op <> " ") <> go y <> ")"
      Sequence [] -> "null"
      Sequence xs -> "(" <> D.joinDoc ", " (map go xs) <> ")"
      SequenceOp op xs -> D.text ("SequenceFunctions::" <> op <> "(") <> go xs <> ")"
      SequenceHead t xs -> "(SequenceFunctions::head(" <> go xs <> ") as " <> D.text (renderCarrier label t) <> ")"
      Enumeration typ c -> D.text (quote (label typ) <> "::" <> quote (label c))
      Construct sym fields -> "new " <> D.text (quote (label sym)) <> "("
        <> D.joinDoc ", " ([D.text (quote p <> " = " <> parameter p) | p <- shapeParameters sym]
          ++ [D.mark owner "constructed-field" (annotation value)
            (D.text (quote (label f)) <> " = " <> go value) | (f,value) <- fields]) <> ")"
      Project value f -> "(" <> go value <> ")." <> D.text (quote (label f))
      Equal left right -> "(" <> go left <> " == " <> go right <> ")"
      Conditional p yes no -> "(if " <> go p <> " ? " <> go yes <> " else " <> go no <> ")"
      BoundCall sym bindings args -> D.text (quote (label sym)) <> "(" <> D.joinDoc ", "
        (map (D.text . parameter) bindings ++ map go args) <> ")"
      Call sym args -> D.text (quote (label sym)) <> "(" <> D.joinDoc ", "
        (map (D.text . parameter) (calcParameters sym) ++ map go args) <> ")"
      Absent -> "null"
    evidence e@(Call sym _) = D.derived "native.call-site" [] (object ["callee" .= sym]) [annotation e]
    evidence e@(Project _ fieldName) = D.derived "native.field-access" [] (object ["field" .= fieldName]) [annotation e]
    evidence e = annotation e
    role Call{} = "call"
    role Project{} = "projection"
    role Construct{} = "construction"
    role Conditional{} = "conditional"
    role Equal{} = "equality"
    role Input{} = "input"
    role _ = "value"

-- Keep every lexical integer within the Pilot parser's signed 32-bit range.
-- Positional arithmetic denotes the same unbounded mathematical natural;
-- this does not impose the evaluator's machine bound on the model's carrier.
naturalText :: Integer -> Text
naturalText n | n < 1000000000 = T.pack (show n)
naturalText n = let (q,r) = n `divMod` 1000000000 in
  "(" <> naturalText q <> " * 1000000000 + " <> T.pack (show r) <> ")"

renderCalculation :: Inventory -> Shapes -> (Text -> Text) -> Calculation -> [Text]
renderCalculation inv shapes label = T.lines . D.render . renderCalculationDoc inv shapes label

renderCalculationDoc :: Inventory -> Shapes -> (Text -> Text) -> Calculation -> D.Doc
renderCalculationDoc inv shapes label c = D.mark owner "calculation"
  (D.derived "native.calculation" [D.root owner "type"] Null []) $
  D.linesDoc ([D.text ("  calc def " <> quote (label owner) <> " {")]
  ++ [D.text ("    in " <> quote (parameterName i) <> " : Base::Anything [0..*];") | i <- parameters]
  ++ [D.text ("    in " <> quote (familyName i) <> " : " <> quote (label (familyRow s)) <> " [0..*];") | (i,s) <- families]
  ++ [D.text ("    in " <> quote ("input" <> T.pack (show i)) <> " : " <> renderCarrier label typ <> " [1];")
     | (i,typ) <- zip [0 :: Int ..] (inputs c)]
  ++ [D.text ("    return 'result' : " <> renderCarrier label (result c) <> " [1] = ")
    <> renderParameterizedDoc label input owner calcBindings shapeBindings binding (body c) <> ";"]
  ++ [D.mark owner "family-domain-contract" (D.derived "native.family-domain-contract" [D.root owner "type"] Null [])
      (D.text ("    assert constraint { " <> condition <> " }")) | condition <- familyDomainConstraints shapes label binding families]
  ++ [D.mark owner "parameter-contract" (D.derived "native.open-parameter-contract" [D.root owner "type"] Null [])
        (D.text ("    assert constraint { " <> condition <> " }"))
     | (value,t) <- [(input i,typ) | (i,typ) <- zip [0 :: Int ..] (inputs c)] ++ [(quote (label owner) <> "::'result'",result c)]
     ,condition <- parameterRefinements shapes label binding value t]
  ++ [let (role,origin) = case M.lookup i contractOrigins of
            Just evidence -> ("index-contract",evidence)
            Nothing -> ("index-contract-boundary",D.generated "native.index-contract")
      in D.mark owner role origin (D.text ("    assert constraint " <> quote ("index-contract-" <> T.pack (show i)) <> " { " <> condition <> " }"))
     | (i,condition) <- zip [0 :: Int ..] (calculationContractsIn shapes label c)] ++ ["  }"])
  where
    owner = calculationSymbol c
    calcParameters s = maybe [] Specialize.nativeParameters (M.lookup s (declarations inv))
    calcFamilies s = maybe [] Specialize.nativeFamilies (M.lookup s (declarations inv))
    calcBindings s = map parameterName (calcParameters s) ++ map (familyName . fst) (calcFamilies s)
    shapeBindings s = maybe [] (\sh -> map parameterName (typeParameters sh) ++ map (familyName . fst) (familyParameters sh)) (M.lookup s shapes)
    parameters = calcParameters owner
    families = calcFamilies owner
    binding p = quote (label owner) <> "::" <> quote p
    contractOrigins = M.union (constructorInputContracts inv shapes c) (constructorResultContracts inv shapes c)
    input i = quote (label owner) <> "::" <> quote ("input" <> T.pack (show i))


-- This rule creates evidence for a fresh assertion, independently of the
-- generated expression histories retained in carrier refinements. It does not
-- erase those histories or promote unrelated result/function contracts.
constructorInputContracts :: Inventory -> Shapes -> Calculation -> M.Map Int D.Origin
constructorInputContracts inv shapes calc = M.fromList
  [(ordinal,evidence) | (ordinal,(position,family,indexPosition,expected,arity)) <- zip [0..] entries
    , Just evidence <- [derive position family indexPosition expected arity]]
  where
    owner = calculationSymbol calc
    entries = [(i,family,j,expected,length indices)
      | (i,Fibre family indices) <- zip [0 :: Int ..] (inputs calc)
      , (j,expected) <- zip [0 :: Int ..] indices]
    derive position family indexPosition expected arity = do
      expectedSlot <- case expected of
        Input slot -> Just slot
        Project (Input slot) _ -> Just slot
        _ -> Nothing
      (sh,con) <- M.lookup owner (constructorTable shapes)
      require (inputs calc == map snd (payload con) && result calc == familyCarrier sh (resultIndices con))
      (schemaType,domains,_) <- constructorSchema inv sh con
      familyShape <- M.lookup family shapes
      require (arity == length (indexTypes familyShape) && expectedSlot >= 0 && expectedSlot < position)
      (domain,_) <- element position domains
      (earlier,_) <- element expectedSlot domains
      expectedType <- element expectedSlot (inputs calc)
      indexType <- element indexPosition (indexTypes familyShape)
      let term = get "term" domain
          eliminations = array (get "eliminations" term)
          contextSlots = reverse [i | (i,(_,cod)) <- zip [0 :: Int ..] (take position domains)
            , get "binds" cod == Bool True]
      require (get "tag" term == String "definition" && get "symbol" term == String family
        && length eliminations == arity)
      elimination <- element indexPosition eliminations
      let argument = get "argument" elimination; info = get "info" argument; variable = get "value" argument
      require (get "tag" elimination == String "apply" && get "hiding" info == String "explicit"
        && get "relevance" info == String "relevant" && get "quantity" info == String "unrestricted"
        && get "tag" variable == String "variable")
      deBruijn <- case get "index" variable of Number n -> toBoundedInteger n; _ -> Nothing
      actualSlot <- element deBruijn contextSlots
      require (actualSlot == expectedSlot)
      (rule,projectionPremises) <- case expected of
        Input _ -> do
          require (expectedType == indexType && null (array (get "eliminations" variable)))
          pure ("native.constructor-input-index",[])
        Project (Input _) fieldName -> do
          record <- checkedProjection fieldName expectedType indexType earlier variable
          pure ("native.constructor-projected-input-index",
            ["projection" .= fieldName,"record" .= record])
        _ -> Nothing
      pure (D.origin rule variable
        (object (["constructor" .= owner,"input" .= position,"family" .= family
          ,"index" .= indexPosition,"indexField" .= indexField family indexPosition
          ,"expectedInput" .= expectedSlot,"bindingSlots" .= contextSlots] ++ projectionPremises))
        [D.origin "native.constructor-telescope" schemaType Null []
        ,D.origin "native.constructor-domain" domain Null []
        ,D.origin "native.constructor-index-input" earlier Null []])
    -- Field admission validates the full record/projection correspondence.
    -- This fresh assertion additionally checks the exact projection use and
    -- its simple checked signature; it does not invent a bare receiver node.
    checkedProjection fieldName expectedType indexType earlier variable = do
      case array (get "eliminations" variable) of
        [e] -> require (get "tag" e == String "project" && get "symbol" e == String fieldName)
        _ -> Nothing
      (record,fieldType) <- M.lookup fieldName (projectionTable shapes)
      require (expectedType == Named record && fieldType == indexType
        && simpleType (Named record) earlier)
      def <- M.lookup fieldName (declarations inv)
      projection <- either (const Nothing) Just (field inv "projection" def)
      require (get "kind" def == String "function" && get "proper" projection == String record
        && get "index" projection == Number 1)
      ty <- either (const Nothing) Just (field inv "type" def)
      let term = get "term" ty; domain = get "domain" term
          info = get "info" domain; codomain = get "codomain" term
      require (get "tag" term == String "pi" && get "hiding" info == String "explicit"
        && get "relevance" info == String "relevant" && get "quantity" info == String "unrestricted"
        && get "binds" codomain `elem` [Bool True,Bool False]
        && simpleType (Named record) (get "type" domain)
        && simpleType indexType (get "body" codomain))
      pure record
    simpleType carrier ty = let term = get "term" ty in
      get "tag" term == String "definition" && null (array (get "eliminations" term))
        && case carrier of
          Boolean -> not (T.null (builtin inv "bool")) && get "symbol" term == String (builtin inv "bool")
          Named name -> get "symbol" term == String name
          _ -> False
    require True = Just ()
    require False = Nothing
    element i xs | i >= 0 = case drop i xs of x:_ -> Just x; _ -> Nothing
                 | otherwise = Nothing

-- Result assertions follow every input assertion, including unsupported ones.
-- Evidence is reconstructed from the terminal checked family application and
-- the selected constructor body, never from equal-looking rendered text.
constructorResultContracts :: Inventory -> Shapes -> Calculation -> M.Map Int D.Origin
constructorResultContracts inv shapes calc = case result calc of
  Fibre family indices -> M.fromList
    [(offset+j,evidence) | (j,expected) <- zip [0..] indices
      , Just evidence <- [derive family (length indices) j expected]]
  _ -> M.empty
  where
    owner = calculationSymbol calc
    offset = sum [length indices | Fibre _ indices <- inputs calc]
    derive family arity indexPosition expected = do
      (sh,con) <- M.lookup owner (constructorTable shapes)
      require (family == shapeSymbol sh && not (isRecord sh)
        && inputs calc == map snd (payload con)
        && result calc == familyCarrier sh (resultIndices con)
        && arity == length (indexTypes sh))
      let values = [Input i | i <- [0..length (inputs calc)-1]]
      require (body calc == Construct family (construction Nothing sh con values))
      (schemaType,domains,resultType) <- constructorSchema inv sh con
      let term = get "term" resultType
          eliminations = array (get "eliminations" term)
          contextSlots = reverse [i | (i,(_,cod)) <- zip [0 :: Int ..] domains
            , get "binds" cod == Bool True]
      require (length eliminations == arity)
      elimination <- element indexPosition eliminations
      indexType <- element indexPosition (indexTypes sh)
      let argument = get "argument" elimination; info = get "info" argument; value = get "value" argument
      require (get "tag" elimination == String "apply" && get "hiding" info == String "explicit"
        && get "relevance" info == String "relevant" && get "quantity" info == String "unrestricted"
        && null (array (get "eliminations" value)))
      (premises,parents) <- case expected of
        Input slot -> do
          require (get "tag" value == String "variable")
          deBruijn <- case get "index" value of Number n -> toBoundedInteger n; _ -> Nothing
          actualSlot <- element deBruijn contextSlots
          actualType <- element slot (inputs calc)
          (domain,_) <- element slot domains
          require (actualSlot == slot && actualType == indexType)
          pure (["kind" .= ("input" :: Text),"expectedInput" .= slot],
            [D.origin "native.constructor-result-input" domain Null []])
        Literal boolean -> do
          let symbol = builtin inv (if boolean then "true" else "false")
          require (indexType == Boolean && not (T.null symbol)
            && get "tag" value == String "constructor" && get "symbol" value == String symbol)
          pure (["kind" .= ("boolean" :: Text),"value" .= boolean,"valueConstructor" .= symbol],[])
        Enumeration valueFamily valueConstructor -> do
          require (indexType == Named valueFamily && get "tag" value == String "constructor"
            && get "symbol" value == String valueConstructor)
          def <- M.lookup valueFamily (declarations inv)
          finite <- either (const Nothing) Just (F.domain inv def)
          require (F.domainSymbol finite == valueFamily && valueConstructor `elem` F.constructors finite)
          pure (["kind" .= ("enumeration" :: Text),"valueFamily" .= valueFamily
            ,"valueConstructor" .= valueConstructor],[])
        _ -> Nothing
      pure (D.origin "native.constructor-result-index" value
        (object (["constructor" .= owner,"family" .= family,"index" .= indexPosition
          ,"indexField" .= indexField family indexPosition,"bindingSlots" .= contextSlots] ++ premises))
        ([D.origin "native.constructor-telescope" schemaType Null []
         ,D.origin "native.constructor-result-type" resultType Null []] ++ parents))
    require True = Just ()
    require False = Nothing
    element i xs | i >= 0 = case drop i xs of x:_ -> Just x; _ -> Nothing
                 | otherwise = Nothing

calculationContracts :: (Text -> Text) -> Calculation -> [Text]
calculationContracts = calculationContractsIn M.empty

calculationContractsIn :: Shapes -> (Text -> Text) -> Calculation -> [Text]
calculationContractsIn shapes label c = concat
  [refinementTextIn shapes label input binding (input i) t | (i,t) <- zip [0 :: Int ..] (inputs c)]
  ++ refinementTextIn shapes label input binding returned (result c)
  ++ [indexEquality shapes label input binding domain (renderWith label input left) right
     | (domain,left,right) <- staticIndexEquations c]
  where
    input i = quote (label (calculationSymbol c)) <> "::" <> quote ("input" <> T.pack (show i))
    returned = quote (label (calculationSymbol c)) <> "::'result'"
    binding p = quote (label (calculationSymbol c)) <> "::" <> quote p

refinementText :: (Text -> Text) -> (Int -> Text) -> Text -> Carrier -> [Text]
refinementText label input = refinementTextIn M.empty label input quote

refinementTextIn :: Shapes -> (Text -> Text) -> (Int -> Text) -> (Text -> Text) -> Text -> Carrier -> [Text]
refinementTextIn _ _ _ _ value Natural = ["(" <> value <> " < *)"]
refinementTextIn shapes label input binding value (Fibre s xs) =
  [indexEquality shapes label input binding domain (value <> "." <> quote (label (indexField s i))) x
  | Just sh <- [M.lookup s shapes]
  , (i,(domain,x)) <- zip [0..] (zip (indexTypes sh) xs)]
  ++ ["(" <> value <> "." <> quote (label (indexField s i)) <> " == " <> renderIndexIn shapes label input binding x <> ")"
     | (i,x) <- zip [0..] xs, M.notMember s shapes]
refinementTextIn _ _ _ _ _ _ = []

-- Type extents are representation bindings, not elements of a source list.
-- Membership constraints still check them; schema equality retains precisely
-- the ordered, nonunique contents when equal bindings use different orders.
indexEquality :: Shapes -> (Text -> Text) -> (Int -> Text) -> (Text -> Text) -> Carrier -> Text -> Expression -> Text
indexEquality shapes label input binding domain value expected =
  let rendered = renderIndexIn shapes label input binding expected
  in case domain of
    Named s | Just sh <- M.lookup s shapes, Just _ <- sequenceElement sh ->
      "SequenceFunctions::equals(" <> value <> "." <> quote sequenceField <> ", (" <> rendered <> ")." <> quote sequenceField <> ")"
    _ -> "(" <> value <> " == " <> rendered <> ")"

renderIndexIn :: Shapes -> (Text -> Text) -> (Int -> Text) -> (Text -> Text) -> Expression -> Text
renderIndexIn shapes label input binding = D.render . renderParameterizedDoc label input "" (const []) bindings binding
  where
    bindings symbol = case M.lookup symbol shapes of
      Just sh -> map parameterName (typeParameters sh) ++ map (familyName . fst) (familyParameters sh)
      Nothing -> []

hasValidity :: Shape -> Bool
hasValidity sh | Just _ <- sequenceElement sh = False
hasValidity sh = not (null (familyParameters sh)) || not (null (typeParameters sh)) || not (isRecord sh) || any refined [t | c <- variants sh,(_,t) <- payload c]
  where refined Natural = True
        refined Fibre{} = True
        refined _ = False

renderShapes :: (Text -> Text) -> Shapes -> [Text]
renderShapes label shapes = renderShapesIn label shapes shapes

-- A selected shape's field/parameter constraints need the complete carrier
-- context, even when its emitted fragment has a separate source boundary.
renderShapesIn :: (Text -> Text) -> Shapes -> Shapes -> [Text]
renderShapesIn label shapes selectedShapes = concatMap renderShape (M.elems selectedShapes)
  where
    parameterFields sh = ["    attribute " <> quote (parameterName i) <> " : Base::Anything [0..*];" | i <- typeParameters sh]
      ++ ["    attribute " <> quote (familyName i) <> " : " <> quote (label (familyRow s)) <> " [0..*];" | (i,s) <- familyParameters sh]
    renderShape sh | Just element <- sequenceElement sh =
      ["  attribute def " <> quote (label (shapeSymbol sh)) <> " {"
      ] ++ parameterFields sh ++ ["    attribute " <> quote sequenceField <> " : " <> renderCarrier label element <> " [0..*] ordered nonunique;"
      ,"    assert constraint 'finite-sequence' { SequenceFunctions::size(" <> quote sequenceField <> ") < * }"]
      ++ ["    assert constraint { " <> quote sequenceField <> "->forAll { in element; " <> condition <> " } }"
         | let value = case element of
                 Named{} -> "(element as " <> renderCarrier label element <> ")"
                 Fibre{} -> "(element as " <> renderCarrier label element <> ")"
                 _ -> "element"
         ,condition <- refinementTextIn shapes label (T.pack . show) quote value element
           ++ parameterRefinements shapes label quote value element]
      ++ ["    assert constraint { " <> condition <> " }" | condition <- familyDomainConstraints shapes label quote (familyParameters sh)]
      ++ ["  }"]
    renderShape sh = (if isRecord sh then [] else
      ["  enum def " <> quote (label (tagType (shapeSymbol sh))) <> " {"]
      ++ ["    enum " <> quote (label (constructorSymbol c)) <> ";" | c <- variants sh] ++ ["  }"])
      ++ ["  attribute def " <> quote (label (shapeSymbol sh)) <> " {"]
      ++ ["    attribute redefines self : " <> quote (label (shapeSymbol sh)) <> ";"
         ,"    assert constraint 'exact-type' { " <> quote (label (shapeSymbol sh))
           <> "::self hastype " <> quote (label (shapeSymbol sh)) <> " }"]
      ++ parameterFields sh
      ++ ["    attribute " <> quote (label (countField (shapeSymbol sh))) <> " : ScalarValues::Natural [1];" | not (null (recursivePeers sh))]
      ++ (if isRecord sh then [] else
        ["    attribute " <> quote (label tagField) <> " : " <> quote (label (tagType (shapeSymbol sh))) <> " [1];"])
      ++ ["    attribute " <> quote (label (indexField (shapeSymbol sh) i)) <> " : " <> renderCarrier label t <> " [1];"
         | (i,t) <- zip [0..] (indexTypes sh)]
      ++ ["    attribute " <> quote (label f) <> " : " <> renderCarrier label ty
           <> (if isRecord sh then " [1];" else " [0..1];")
         | c <- variants sh,(f,ty) <- payload c]
      ++ (if not (hasValidity sh) then [] else
        ["    assert constraint 'valid-payload' { " <> quote (label (validitySymbol (shapeSymbol sh)))
          <> "(" <> quote (label (shapeSymbol sh)) <> "::self) }"])
      ++ ["  }"]
      ++ (if not (hasValidity sh) then [] else
        ["  constraint def " <> quote (label (validitySymbol (shapeSymbol sh))) <> " {"
        ,"    in 'value' : " <> quote (label (shapeSymbol sh)) <> " [1];"
        ,"    " <> validity shapes label sh
        ,"  }"])

parameterRefinements :: Shapes -> (Text -> Text) -> (Text -> Text) -> Text -> Carrier -> [Text]
parameterRefinements _ _ parameter value (TypeParameter i) =
  ["SequenceFunctions::includes(" <> parameter (parameterName i) <> ", " <> value <> ")"]
parameterRefinements shapes _ parameter value (Named s) =
  ["SequenceFunctions::includesOnly(" <> value <> "." <> quote (parameterName i) <> ", " <> parameter (parameterName i) <> ")"
  | sh <- maybe [] (:[]) (M.lookup s shapes),i <- typeParameters sh]
  ++ ["SequenceFunctions::includesOnly(" <> value <> "." <> quote (familyName i) <> ", " <> parameter (familyName i) <> ")"
     | sh <- maybe [] (:[]) (M.lookup s shapes),(i,_) <- familyParameters sh]
parameterRefinements shapes label parameter value (Fibre s _) = parameterRefinements shapes label parameter value (Named s)
parameterRefinements _ _ _ _ _ = []

familyDomainConstraints :: Shapes -> (Text -> Text) -> (Text -> Text) -> [(Int,Text)] -> [Text]
familyDomainConstraints shapes label binding families =
  [binding (familyName slot) <> "->forAll { in row; " <> condition <> " }"
  | (slot,symbol) <- families,Just member <- [M.lookup symbol shapes]
  ,(i,domain) <- zip [0..] (indexTypes member)
  ,let field = "(row as " <> quote (label (familyRow symbol)) <> ")." <> quote (label (indexField (familyRow symbol) i))
  ,condition <- refinementTextIn shapes label (T.pack . show) binding field domain
    ++ parameterRefinements shapes label binding field domain]

validity :: Shapes -> (Text -> Text) -> Shape -> Text
validity shapes label sh = case constraints of
  [] -> "true"
  _ -> T.intercalate " and " constraints
  where
    selected c = "'value'." <> quote (label tagField) <> " == " <> quote (label (tagType (shapeSymbol sh)))
      <> "::" <> quote (label (constructorSymbol c))
    guarded c expr = if isRecord sh then expr else "(if " <> selected c <> " ? " <> expr <> " else true)"
    fieldText f = "'value'." <> quote (label f)
    constraints = (if isRecord sh then [] else
      ["(SequenceFunctions::size(" <> fieldText f <> ") == (if " <> selected c <> " ? 1 else 0))"
      | c <- variants sh,(f,_) <- payload c])
      ++ [guarded c (indexEquality shapes label (\j -> fieldText (fst (payload c !! j))) fieldText domain
           (fieldText (indexField (shapeSymbol sh) i)) e)
         | c <- variants sh,(i,(domain,e)) <- zip [0..] (zip (indexTypes sh) (resultIndices c))]
      ++ [guarded c constraint | c <- variants sh,(f,t) <- payload c
         ,constraint <- refinementTextIn shapes label (\j -> fieldText (fst (payload c !! j))) fieldText (fieldText f) t
           ++ parameterRefinements shapes label fieldText (fieldText f) t]
      ++ [condition | (i,t) <- zip [0..] (indexTypes sh),condition <- parameterRefinements shapes label fieldText (fieldText (indexField (shapeSymbol sh) i)) t]
      ++ familyDomainConstraints shapes label fieldText (familyParameters sh)
      ++ (if null (recursivePeers sh) then [] else
        ["(" <> fieldText (countField (shapeSymbol sh)) <> " < *)"]
        ++ [guarded c ("(" <> fieldText (countField (shapeSymbol sh)) <> " == 1"
            <> T.concat [" + " <> fieldText f <> "." <> quote (label (countField owner)) | (f,t) <- payload c,owner <- recursiveOwner sh t] <> ")") | c <- variants sh]
        ++ [guarded c ("(" <> fieldText f <> "." <> quote (label (countField owner)) <> " < " <> fieldText (countField (shapeSymbol sh)) <> ")")
          | c <- variants sh,(f,t) <- payload c,owner <- recursiveOwner sh t])
      ++ case relationParameter sh of
        Nothing -> []
        Just slot -> [fieldText (familyName slot) <> "->exists { in row; " <> T.intercalate " and "
          (["((row as " <> quote (label (familyRow (shapeSymbol sh))) <> ")." <> quote (label (indexField (familyRow (shapeSymbol sh)) i)) <> " == " <> fieldText (indexField (shapeSymbol sh) i) <> ")" | i <- [0..length (indexTypes sh)-1]]
          ++ ["((row as " <> quote (label (familyRow (shapeSymbol sh))) <> ")." <> quote (label (familyValue (familyRow (shapeSymbol sh)))) <> " == " <> fieldText (familyValue (shapeSymbol sh)) <> ")"]) <> " }"]

-- All symbols used by the renderer, including generated domain-specific
-- helpers, participate in the common name-collision check.
references :: Shapes -> [Text]
references shapes = concat
  [[shapeSymbol sh] ++ map constructorSymbol (variants sh) ++ concatMap (map fst . payload) (variants sh)
    ++ [countField (shapeSymbol sh) | not (null (recursivePeers sh))]
    ++ [indexField (shapeSymbol sh) i | i <- [0..length (indexTypes sh)-1]]
    ++ (if hasValidity sh then [validitySymbol (shapeSymbol sh)] else [])
    ++ (if isRecord sh then [] else [tagType (shapeSymbol sh),tagField]) | sh <- M.elems shapes]

generatedNames :: (Text -> Text) -> Shapes -> M.Map Text Text
generatedNames display shapes = M.fromList $ concat
  [[(tagType (shapeSymbol sh),display (shapeSymbol sh) <> ".constructor-tag")
   ,(validitySymbol (shapeSymbol sh),display (shapeSymbol sh) <> ".payload-valid")]
    ++ [(countField (shapeSymbol sh),display (shapeSymbol sh) <> ".node-count") | not (null (recursivePeers sh))]
    ++ [(indexField (shapeSymbol sh) i,display (shapeSymbol sh) <> ".index" <> T.pack (show i))
       | i <- [0..length (indexTypes sh)-1]]
    ++ [(familyValue (shapeSymbol sh),display (shapeSymbol sh) <> ".value") | relationParameter sh /= Nothing || ".relation-row" `T.isSuffixOf` shapeSymbol sh]
    ++ [(familyRow (shapeSymbol sh),display (shapeSymbol sh) <> ".relation-row") | relationParameter sh /= Nothing]
    ++ [(f,display (constructorSymbol c) <> ".payload" <> T.pack (show i))
       | c <- variants sh,(i,(f,_)) <- zip [0 :: Int ..] (payload c),not (isRecord sh)]
  | sh <- M.elems shapes]

-- Helpers consume the already admitted shape without changing its semantics.
-- Walk the actual checked telescope to locate each domain; never search for
-- equal types, skip NoAbs inputs, or manufacture a path from an input number.
constructorCalculations :: Inventory -> Shapes -> [Calculation]
constructorCalculations inv shapes =
  [let schema = constructorSchema inv sh c
       premises i f cod = object ["constructor" .= constructorSymbol c,"family" .= shapeSymbol sh
         ,"position" .= i,"field" .= f,"binds" .= get "binds" cod]
       input i f = case schema of
         Just (ty,domains,_) | (domain,cod):_ <- drop i domains ->
           Annotated (D.origin "native.constructor-input" domain (premises i f cod)
             [D.origin "native.constructor-telescope" ty Null []]) (Input i)
         _ -> Annotated (D.generated "native.constructor-input") (Input i)
       values = [input i f | (i,(f,_)) <- zip [0 :: Int ..] (payload c)]
       rootOrigin = case schema of
         Just (ty,_,_) -> D.origin "native.constructor-helper" ty
           (object ["constructor" .= constructorSymbol c,"family" .= shapeSymbol sh
             ,"arity" .= length (payload c)]) []
         _ -> D.generated "native.constructor-helper"
   in Calculation (constructorSymbol c) (map snd (payload c)) (familyCarrier sh (resultIndices c))
        (Annotated rootOrigin (Construct (shapeSymbol sh) (construction Nothing sh c values))) []
    | sh <- M.elems shapes,c <- variants sh,M.member (constructorSymbol c) (declarations inv)]

primitiveOperation :: Text -> Maybe (Text,Carrier)
primitiveOperation p = lookup p
  [("PrimNatPlus",("+",Natural)),("PrimNatMinus",("monus",Natural)),("PrimNatTimes",("*",Natural))
  ,("PrimNatEquality",("==",Boolean)),("PrimNatLess",("<",Boolean))]

naturalCalculations :: Inventory -> [Calculation]
naturalCalculations inv =
  [Calculation s args Natural (Annotated (D.derived "native.natural-constructor" [D.root s "type"] Null []) expr) []
  | (key,args,expr) <- [("zero",[],NumberLiteral 0),("suc",[Natural],Numeric "+" (Input 0) (NumberLiteral 1))]
  , let s = builtin inv key, not (T.null s), any ((== s) . fst) (S.toList (required inv))]

constructorSchema :: Inventory -> Shape -> Constructor -> Maybe (Value,[(Value,Value)],Value)
constructorSchema inv sh c = do
  def <- M.lookup (constructorSymbol c) (declarations inv)
  if get "kind" def /= String "constructor" then Nothing else Just ()
  ty <- either (const Nothing) Just (field inv "type" def)
  (domains,resultType) <- telescope ty
  let resultTerm = get "term" resultType
  if length domains == length (payload c) && get "tag" resultTerm == String "definition"
      && get "symbol" resultTerm == String (shapeSymbol sh)
    then Just (ty,domains,resultType) else Nothing
  where
    telescope ty = case get "tag" (get "term" ty) of
      String "pi" -> do
        let term = get "term" ty; dom = get "type" (get "domain" term); cod = get "codomain" term
        if get "binds" cod `elem` [Bool True,Bool False] && get "$occurrence" dom /= Null
          then Just () else Nothing
        (rest,resultType) <- telescope (get "body" cod)
        pure ((dom,cod):rest,resultType)
      _ | get "$occurrence" ty /= Null -> Just ([],ty)
        | otherwise -> Nothing

carrierReport :: (Text -> Text) -> Shapes -> Value
carrierReport label shapes = toJSON [object
  ["symbol" .= shapeSymbol sh,"target" .= target (shapeSymbol sh)
  ,"recursivePeers" .= recursivePeers sh
  ,"nodeCountTarget" .= (if null (recursivePeers sh) then Null else String (target (shapeSymbol sh) <> "::" <> quote (label (countField (shapeSymbol sh)))))
  ,"typeParameters" .= [object ["position" .= i,"type" .= ("Base::Anything" :: Text)
    ,"representation" .= ("native-type-extent" :: Text),"multiplicity" .= ("0..*" :: Text)
    ,"target" .= (target (shapeSymbol sh) <> "::" <> quote (parameterName i))] | i <- typeParameters sh]
  ,"familyParameters" .= [object ["position" .= i,"rowType" .= target (familyRow s),"target" .= (target (shapeSymbol sh) <> "::" <> quote (familyName i))] | (i,s) <- familyParameters sh]
  ,"relationParameter" .= relationParameter sh
  ,"kind" .= (case sequenceElement sh of Just _ -> "sequence"; Nothing -> if isRecord sh then "record" else "sum" :: Text)
  ,"sequence" .= (case sequenceElement sh of
      Just element -> object ["elementType" .= renderCarrier label element,"ordered" .= True,"unique" .= False
        ,"itemsTarget" .= (target (shapeSymbol sh) <> "::" <> quote sequenceField),"finite" .= True]
      Nothing -> Null)
  ,"admissibility" .= (if hasValidity sh then String (target (validitySymbol (shapeSymbol sh))) else Null)
  ,"indices" .= [object ["position" .= i,"type" .= renderCarrier label t
    ,"target" .= (target (shapeSymbol sh) <> "::" <> quote (label (indexField (shapeSymbol sh) i)))]
    | (i,t) <- zip [0 :: Int ..] (indexTypes sh)]
  ,"constructors" .= [object ["symbol" .= constructorSymbol c,"target" .= target (constructorSymbol c)
    ,"resultIndices" .= map (renderIndexIn shapes label (\i -> quote (label (fst (payload c !! i)))) quote) (resultIndices c)
    ,"payload" .= [object ["position" .= i,"field" .= f
      ,"type" .= renderCarrier label typ
      ,"refinements" .= refinementTextIn shapes label (\j -> quote (label (fst (payload c !! j)))) quote (quote (label f)) typ
      ,"target" .= (case sequenceElement sh of
          Just _ -> Null
          Nothing -> String (target (shapeSymbol sh) <> "::" <> quote (label f)))]
      | (i,(f,typ)) <- zip [0 :: Int ..] (payload c)]] | c <- variants sh]] | sh <- M.elems shapes]
  where target s = "AgdaModel::" <> quote (label s)
