{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Closed, acyclic products and sums. Every payload position is retained;
-- named types, constructor identities and projections come from checked Agda.
module Agda2SysML.AlgebraicTarget
  ( Carrier(..), Shape(..), pattern Shape, Constructor(..), Calculation(..), Expression(Input, Argument, Literal, NumberLiteral, Numeric, Sequence, SequenceOp, SequenceHead, Enumeration, Construct, Project, Equal, Conditional, Call, Apply, Absent, Lambda, Iterator)
  , discover, function, symbols, renderShapes, renderShapesIn, renderCalculation, renderCalculationDoc, references
  , constructorCalculations, naturalCalculations, generatedNames, carrierReport, functions, calls, calculationContracts, calculationContractsIn, dependencies
  , EqualityStatement(..), equalityStatements, renderStatementDoc ) where

import qualified Agda2SysML.Derivation as D
import Agda2SysML.Inventory hiding (field)
import Agda2SysML.Diagnostic (Refusal, Category(..), refuse, refusal, context, field)
import qualified Agda2SysML.FiniteTarget as F
import qualified Agda2SysML.Specialize as Specialize
import Control.Monad (unless, forM, forM_, foldM, (>=>))
import Data.Graph (SCC(..), stronglyConnComp)
import Data.Aeson
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger, floatingOrInteger)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

data Carrier = Boolean | Natural | AnyValue | TypeParameter Int | Named Text | Fibre Text [Expression]
  | Callable [Carrier] Carrier deriving (Eq, Show)
data Constructor = Constructor
  { constructorSymbol :: Text, payload :: [(Text,Carrier)], resultIndices :: [Expression] } deriving (Eq, Show)
data Shape = ShapeData
  { shapeSymbol :: Text, isRecord :: Bool, variants :: [Constructor], indexTypes :: [Carrier]
  , sequenceElement :: Maybe Carrier, typeParameters :: [Int]
  , familyParameters :: [(Int,Text)], relationParameter :: Maybe Int, recursivePeers :: [Text]
  , schemaExtent :: Bool, storedSchema :: Maybe Text, contextIndices :: [Int]
  , relationRowOf :: Maybe Text } deriving (Eq, Show)
pattern Shape :: Text -> Bool -> [Constructor] -> [Carrier] -> Shape
pattern Shape s r cs is <- ShapeData s r cs is _ _ _ _ _ _ _ _ _ where Shape s r cs is = ShapeData s r cs is Nothing [] [] Nothing [] False Nothing [] Nothing
data Expression = Annotated D.Origin Expression
  | NInput Int
  | NArgument Int
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
  | NApply Expression [Expression]
  | NBoundCall Text [Text] [Expression]
  | NAbsent
  | NExtent Text
  | NIterator Text Carrier
  | NCollect Text Carrier Expression Expression
  | NCast Text Expression
  | NLambda [(Text,Carrier)] Carrier Expression
  deriving Show

unmark :: Expression -> Expression
unmark (Annotated _ x) = unmark x
unmark x = x

instance Eq Expression where
  x == y | NArgument i <- unmark x, NArgument j <- unmark y = i == j
  x == y | NApply f a <- unmark x, NApply g b <- unmark y = f == g && a == b
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
  x == y | NExtent a <- unmark x, NExtent b <- unmark y = a == b
  x == y | NIterator a t <- unmark x, NIterator b u <- unmark y = a == b && t == u
  x == y | NCollect a t xs v <- unmark x, NCollect b u ys w <- unmark y = (a,t,xs,v) == (b,u,ys,w)
  x == y | NCast t a <- unmark x, NCast u b <- unmark y = (t,a) == (u,b)
  x == y | NLambda as t a <- unmark x, NLambda bs u b <- unmark y =
    lambdaForm as t a == lambdaForm bs u b
  _ == _ = False

-- Local binder spelling is not part of a closure's meaning. Negative argument
-- positions are comparison-only bound names; checked callback arguments use
-- nonnegative positions. Normalize the entire nested scope at once so an inner
-- binder cannot be confused with an outer capture.
lambdaForm :: [(Text,Carrier)] -> Carrier -> Expression -> ([Carrier],Carrier,Expression)
lambdaForm args out body = let (types,_,result,value) = bind M.empty 0 args out body
  in (map snd types,result,value)
  where
    bind names next [] result value = ([],next,mapCarrier (go names next) result,go names next value)
    bind names next ((name,typ):rest) result value =
      let domain = mapCarrier (go names next) typ
          (types,final,result',value') = bind (M.insert name next names) (next+1) rest result value
      in (("$closure" <> T.pack (show next),domain):types,final,result',value')
    go names next = mapExpression $ \e -> case e of
      Iterator name _ | Just i <- M.lookup name names -> Just (Argument (-1-i))
      Lambda inputs result value -> let (types,_,result',value') = bind names next inputs result value
        in Just (Lambda types result' value')
      Collect name typ xs value -> Just (Collect name (mapCarrier (go names next) typ)
        (go names next xs) (go (M.delete name names) next value))
      _ -> Nothing
pattern Input :: Int -> Expression
pattern Input i <- (unmark -> NInput i) where Input i = NInput i
pattern Argument :: Int -> Expression
pattern Argument i <- (unmark -> NArgument i) where Argument i = NArgument i
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
pattern Apply :: Expression -> [Expression] -> Expression
pattern Apply f x <- (unmark -> NApply f x) where Apply f x = NApply f x
pattern BoundCall :: Text -> [Text] -> [Expression] -> Expression
pattern BoundCall s bindings xs <- (unmark -> NBoundCall s bindings xs) where BoundCall s bindings xs = NBoundCall s bindings xs

callParts :: Expression -> Maybe (Text,[Expression])
callParts expression = case unmark expression of
  NCall s xs -> Just (s,xs)
  NBoundCall s _ xs -> Just (s,xs)
  _ -> Nothing
pattern Absent :: Expression
pattern Absent <- (unmark -> NAbsent) where Absent = NAbsent
pattern Extent :: Text -> Expression
pattern Extent name <- (unmark -> NExtent name) where Extent name = NExtent name
pattern Iterator :: Text -> Carrier -> Expression
pattern Iterator name typ <- (unmark -> NIterator name typ) where Iterator name typ = NIterator name typ
pattern Collect :: Text -> Carrier -> Expression -> Expression -> Expression
pattern Collect name typ values body <- (unmark -> NCollect name typ values body) where Collect name typ values body = NCollect name typ values body
pattern Cast :: Text -> Expression -> Expression
pattern Cast typ value <- (unmark -> NCast typ value) where Cast typ value = NCast typ value
pattern Lambda :: [(Text,Carrier)] -> Carrier -> Expression -> Expression
pattern Lambda inputs result body <- (unmark -> NLambda inputs result body) where Lambda inputs result body = NLambda inputs result body
{-# COMPLETE Input, Argument, Literal, NumberLiteral, Numeric, Sequence, SequenceOp, SequenceHead, Enumeration, Construct, Project, Equal, Conditional, Call, Apply, Absent, Extent, Iterator, Collect, Cast, Lambda #-}

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
      Apply f x -> origins f ++ concatMap origins x
      Collect _ _ xs body -> origins xs ++ origins body
      Cast _ value -> origins value
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
carrierIn inv finite helpers shapes env ty | get "tag" (get "term" ty) == String "native-callable" = do
  let term = get "term" ty
      legacy = get "inputs" term == Null
      domains = if legacy then [get "input" term] else array (get "inputs" term)
  unless (not (null domains)) (refuse Syntax "Callback requires a nonempty argument telescope")
  (types,context) <- foldM (\(prior,context) domain -> do
    typ <- carrierIn inv finite helpers shapes context domain
    let context' = if legacy && get "binds" term /= Bool True then context else (typ,Argument (length prior)):context
    pure (prior ++ [typ],context')) ([],env) domains
  Callable types <$> carrierIn inv finite helpers shapes context (get "result" term)
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
  unless (canonical actual == canonical expected) (refuse Semantics
    ("Index expression has the wrong admitted domain: expected " <> describe (canonical expected)
      <> "; actual " <> describe (canonical actual)))
  pure (normalize e)
  where
    projections = projectionTable shapes
    canonical (Fibre family indices) = case M.lookup family shapes of
      Just sh | length indices == length (indexTypes sh) -> Fibre family [case domain of
          Named owner | Just shape <- M.lookup owner shapes,Just _ <- sequenceElement shape,not (schemaExtent shape) ->
            sequenceIdentity shapes helpers (Project (expand helpers value) sequenceField)
          _ -> expand helpers value
        | (domain,value) <- zip (indexTypes sh) indices]
      _ -> mapCarrier (expand helpers) (Fibre family indices)
    canonical typ = typ
    describe (Fibre s xs) = s <> "[" <> T.intercalate "," (map (renderWith id (T.pack . show)) xs) <> "]"
    describe typ = T.pack (show typ)
    infer term = fmap (\(typ,e) -> (typ,located "native.index-term" term (toJSON [renderWith id (T.pack . show) x | (_,x) <- env]) e)) $ do
      let es = array (get "eliminations" term)
      case string (get "tag" term) of
        "native-lambda" -> do
          let types = array (get "inputs" term)
          unless (not (null types)) (refuse Syntax "Malformed index lambda telescope")
          (locals,context) <- foldM (\(locals,context) ty -> do
            domain <- carrierIn inv finite helpers shapes context ty
            let name = "lambdaArgument" <> T.pack (show (length env + length locals))
            pure (locals ++ [(name,domain)],(domain,Iterator name domain):context)) ([],env) types
          out <- carrierIn inv finite helpers shapes context (get "result" term)
          value <- indexExpression inv finite helpers shapes context out (get "body" term)
          let rebase = mapCarrier (mapExpression (\e -> case e of
                Iterator name _ -> Argument <$> lookup name (zip (map fst locals) [0..])
                _ -> Nothing))
          eliminate (Callable (map (rebase . snd) locals) (rebase out),Lambda locals out value) es
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
            def <- maybe (refuse Syntax "Missing computed index declaration") Right
              (M.lookup (calculationSymbol helper) (declarations inv))
            p <- field inv "projection" def
            dropped <- if p == Null || get "nativeFullArguments" term == Bool True then Right 0
              else subtract 1 <$> integer (get "index" p)
            unless (dropped >= 0 && dropped <= length (inputs helper))
              (refuse Syntax "Invalid computed index omitted prefix")
            let supplied = drop dropped (inputs helper)
                (apps,rest) = splitAt (length supplied) es
            unless (length apps == length supplied) (refuse Syntax "Computed index helper arity mismatch")
            actuals <- traverse (\arg -> applicationValue arg >>= infer) apps
            known <- foldM (recoverCarrierInputs shapes canonicalIndex) M.empty (zip supplied (map fst actuals))
            prefix <- traverse (\i -> maybe (refuse Representation "Cannot recover omitted computed index") Right
              (M.lookup i known)) [0..dropped-1]
            let args = prefix ++ map snd actuals
            forM_ (zip supplied actuals) $ \(domain,value) ->
              unless (canonical (fst value) == canonical (mapCarrier (instantiate args) domain))
                (refuse Semantics "Computed index helper argument domain mismatch")
            let bindings = case M.lookup (calculationSymbol helper) (declarations inv) of
                  Just def -> map parameterName (Specialize.nativeParameters def)
                    ++ map (familyName . fst) (Specialize.nativeFamilies def)
                  Nothing -> []
            eliminate (mapCarrier (instantiate args) (result helper),BoundCall (calculationSymbol helper) bindings args) rest
          Nothing -> case es of
            arg:rest -> do
              receiver <- applicationValue arg >>= infer
              projected <- project receiver (string (get "symbol" term))
              eliminate projected rest
            _ -> refuse Representation "Computed index requires an admitted finite helper or proper record projection"
        _ -> refuse Syntax "Unsupported finite index expression"
    eliminate value [] = Right value
    eliminate (Callable domains out,fn) es@(_:_) = do
      unless (length es >= length domains) (refuse Representation "Partial callback application requires runtime closure construction")
      values <- foldM (\prior (domain,e) -> do
        value <- applicationValue e >>= indexExpression inv finite helpers shapes env (applyCallback prior domain)
        pure (prior ++ [value])) [] (zip domains es)
      eliminate (applyCallback values out,Apply fn values) (drop (length domains) es)
    eliminate value (e:es) = do
      unless (get "tag" e == String "project") (refuse Syntax "Computed index elimination")
      projected <- project value (string (get "symbol" e))
      eliminate projected es
    project (actual,value) f = do
      (owner,typ) <- maybe (refuse Representation ("Index function is not an admitted proper projection: " <> f)) Right (M.lookup f projections)
      unless (recordOwner actual owner) (refuse Semantics "Index projection belongs to another record")
      d <- maybe (refuse Syntax "Missing index projection declaration") Right (M.lookup f (declarations inv))
      p <- field inv "projection" d
      unless (get "proper" p == String owner && get "index" p == Number 1)
        (refuse Syntax "Index expression uses invalid projection metadata")
      pure (projectedCarrier shapes actual value typ,Project value f)
    canonicalIndex domain value = case domain of
        Named owner | Just sh <- M.lookup owner shapes,Just _ <- sequenceElement sh,not (schemaExtent sh) ->
          sequenceIdentity shapes helpers (Project (expand helpers value) sequenceField)
        _ -> normalize (expand helpers value)

-- Recover only direct signature-local index variables from checked argument
-- fibres. Repeated occurrences must agree; arbitrary computations are not inverted.
recoverCarrierInputs :: Shapes -> (Carrier -> Expression -> Expression)
  -> M.Map Int Expression -> (Carrier,Carrier) -> Either Refusal (M.Map Int Expression)
recoverCarrierInputs shapes canonical known (Fibre s xs,Fibre t ys)
  | s == t && length xs == length ys,Just sh <- M.lookup s shapes =
    foldM bind known (zip3 (indexTypes sh) xs ys)
    where
      bind table (domain,Input i,y) = case M.lookup i table of
        Nothing -> Right (M.insert i y table)
        Just x | canonical domain x == canonical domain y -> Right table
        _ -> refuse Semantics "Inconsistent omitted index"
      bind table _ = Right table
recoverCarrierInputs _ _ known _ = Right known

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
    Apply f x -> Apply (go f) (map go x)
    Iterator name typ -> Iterator name (mapCarrier go typ)
    Collect name typ xs body -> Collect name (mapCarrier go typ) (go xs) (go body)
    Cast typ value -> Cast typ (go value)
    Lambda args out body -> Lambda [(name,mapCarrier go ty) | (name,ty) <- args] (mapCarrier go out) (go body)
    _ -> e
  where go = mapExpression replace

mapCarrier :: (Expression -> Expression) -> Carrier -> Carrier
mapCarrier f (Callable a b) = Callable (map (mapCarrier f) a) (mapCarrier f b)
mapCarrier f (Fibre s xs) = Fibre s (map (normalize . f) xs)
mapCarrier _ t = t

applyCallback :: [Expression] -> Carrier -> Carrier
applyCallback values = mapCarrier (mapExpression (\e -> case e of
  Argument i | i >= 0 && i < length values -> Just (values !! i)
  _ -> Nothing))

instantiate :: [Expression] -> Expression -> Expression
instantiate args = mapExpression (\e -> case e of Input i | i >= 0 && i < length args -> Just (args !! i); _ -> Nothing)

-- Beta substitution must not capture a caller's iterator under a nested
-- lambda or collect binder. Freshen those binders before inserting arguments.
applyLambda :: Expression -> [Expression] -> Maybe Expression
applyLambda (Lambda args _ body) values | length args == length values =
  Just (go occupied (M.fromList (zip (map fst args) values)) body)
  where
    occupied = S.unions (map names (body:values)) `S.union` S.fromList (map fst args)
    fresh used = head ["$beta" <> T.pack (show i) | i <- [0 :: Int ..],S.notMember ("$beta" <> T.pack (show i)) used]
    go used bindings = mapExpression $ \e -> case e of
      Iterator name _ -> M.lookup name bindings
      Lambda inputs result value -> Just (bind used bindings inputs result value)
      Collect name typ xs value ->
        let name' = fresh used; domain = mapCarrier (go used bindings) typ
        in Just (Collect name' domain (go used bindings xs)
          (go (S.insert name' used) (M.insert name (Iterator name' domain) bindings) value))
      _ -> Nothing
    bind used bindings [] result value = Lambda [] (mapCarrier (go used bindings) result) (go used bindings value)
    bind used bindings ((name,typ):rest) result value =
      let name' = fresh used; domain = mapCarrier (go used bindings) typ
      in case bind (S.insert name' used) (M.insert name (Iterator name' domain) bindings) rest result value of
        Lambda inputs result' value' -> Lambda ((name',domain):inputs) result' value'
        _ -> error "lambda binding lost its telescope"
    carrierNames (Callable inputs result) = S.unions (map carrierNames (result:inputs))
    carrierNames (Fibre _ xs) = S.unions (map names xs)
    carrierNames _ = S.empty
    names e = case e of
      Iterator name typ -> S.insert name (carrierNames typ)
      Lambda inputs result value -> S.unions (names value:carrierNames result:
        [S.insert name (carrierNames typ) | (name,typ) <- inputs])
      Collect name typ xs value -> S.insert name (S.unions [carrierNames typ,names xs,names value])
      Construct _ fs -> S.unions (map (names . snd) fs)
      Project x _ -> names x
      Equal x y -> names x `S.union` names y
      Numeric _ x y -> names x `S.union` names y
      Sequence xs -> S.unions (map names xs)
      SequenceOp _ x -> names x
      SequenceHead typ x -> carrierNames typ `S.union` names x
      Conditional p x y -> S.unions (map names [p,x,y])
      Call _ xs -> S.unions (map names xs)
      Apply f xs -> S.unions (map names (f:xs))
      Cast _ x -> names x
      _ -> S.empty
applyLambda _ _ = Nothing

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
normalizeStep (Apply f x) = Apply (normalize f) (map normalize x)
normalizeStep (Collect name typ xs body) = Collect name typ (normalize xs) (normalize body)
normalizeStep (Cast typ value) = Cast typ (normalize value)
normalizeStep (Lambda args out body) = Lambda args out (normalize body)
normalizeStep (Equal x y) = Equal (normalize x) (normalize y)
normalizeStep (Numeric op x y) = case (op,normalize x,normalize y) of
  ("+",a,b) -> naturalSum a b
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

-- Comparison may identify a sequence reconstructed from its head and tail.
-- Keep that reconstruction during computation: a checked nonempty branch
-- lets recursive index helpers reduce, whereas an opaque sequence does not.
sequenceIdentity :: Shapes -> Helpers -> Expression -> Expression
sequenceIdentity shapes helpers = mapExpression join . normalize
  where
    -- Rewrapping the contents of a typed list-valued call or field preserves
    -- that exact carrier. This is congruence inside later index calls, not
    -- inversion of the helper or equality between different list carriers.
    join (Construct owner [(field,Project value member)])
      | field == sequenceField,member == sequenceField
      ,Just sh <- M.lookup owner shapes,not (schemaExtent sh),Just _ <- sequenceElement sh
      ,valueCarrier value == Just (Named owner) = Just value
    join (Sequence xs) = Just (normalize (Sequence (foldr rejoin [] (map (sequenceIdentity shapes helpers) xs))))
    join _ = Nothing
    valueCarrier (Call symbol _) = result <$> M.lookup symbol helpers
    valueCarrier (Project _ member) = case
      [typ | sh <- M.elems shapes,con <- variants sh,(field,typ) <- payload con,field == member] of
        typ:rest | all (== typ) rest -> Just typ
        _ -> Nothing
    valueCarrier _ = Nothing
    rejoin (SequenceHead _ xs) (SequenceOp "tail" ys:rest) | xs == ys = xs:rest
    rejoin x rest = x:rest

-- Natural addition is associative and constants commute with its operands.
-- Preserve symbolic operand order and attach the constant to the first one:
-- this also exposes a branch-local (predecessor n + 1) = n equation.
-- Subtraction and residual calls remain indivisible operands.
naturalSum :: Expression -> Expression -> Expression
naturalSum x y = case terms of
  [] -> NumberLiteral constant
  first:rest -> foldl (Numeric "+")
    (if constant == 0 then first else Numeric "+" first (NumberLiteral constant)) rest
  where
    (terms,constant) = collect (Numeric "+" x y)
    collect (Numeric "+" a b) = let (as,m) = collect a; (bs,n) = collect b in (as ++ bs,m+n)
    collect (NumberLiteral n) = ([],n)
    collect value = ([value],0)

-- Expansion uses independently checked helpers and certified finite normal
-- forms. A recursive symbol unfolds once per path; residual calls stay opaque.
-- Emission retains the original native calls and their checked dependency graph.
expand :: Helpers -> Expression -> Expression
expand = expandWith id

-- Branch facts also apply to expressions exposed by unfolding a helper. Keep
-- the same expansion-path guard while rewriting; restarting expansion after
-- each rewrite would unfold recursive calls indefinitely.
expandWith :: (Expression -> Expression) -> Helpers -> Expression -> Expression
expandWith rewrite helpers = go S.empty . rewrite
  where
    go = step
    step seen (Call s args) = case M.lookup s helpers of
      Just helper | S.notMember s seen ->
        let arguments = map (go seen) args
            unfolded = go (S.insert s seen) (rewrite (instantiate arguments (body helper)))
        in case unfolded of
          Conditional{} | S.member s recursive -> Call s arguments
          _ -> unfolded
      _ -> Call s (map (go seen) args)
    -- Unfolding can expose a projection already constrained by this branch.
    -- Apply that fact once, without recursively rewriting its replacement.
    step seen (Project x f) = normalize (rewrite (normalize (Project (go seen x) f)))
    step seen (Apply f x) = let fn = go seen f; values = map (go seen) x
      in maybe (Apply fn values) (go seen . rewrite) (applyLambda fn values)
    step seen (Collect name typ xs value) = Collect name (mapCarrier (go seen) typ) (go seen xs) (go seen value)
    step seen (Cast typ value) = Cast typ (go seen value)
    step seen (Construct s fs) = Construct s [(f,go seen x) | (f,x) <- fs]
    step seen (Sequence xs) = normalize (Sequence (map (go seen) xs))
    step seen (SequenceOp op xs) = normalize (SequenceOp op (go seen xs))
    step seen (SequenceHead t xs) = normalize (SequenceHead (mapCarrier (go seen) t) (go seen xs))
    step seen (Numeric op x y) = normalize (rewrite (normalize (Numeric op (go seen x) (go seen y))))
    step seen (Equal x y) = case (go seen x,go seen y) of
      (Literal a,Literal b) -> Literal (a == b)
      (Enumeration a x',Enumeration b y') -> Literal (a == b && x' == y')
      (x',y') | x' == y' -> Literal True
              | otherwise -> Equal x' y'
    step seen (Conditional p yes no) = case go seen p of
      Literal True -> go seen yes
      Literal False -> go seen no
      p' -> let yes' = go seen yes; no' = go seen no in
        if yes' == no' then yes' else Conditional p' yes' no'
    step _ e = e
    recursive = S.fromList (concat [ss | CyclicSCC ss <- stronglyConnComp
      [(s,s,S.toList (calls (body c))) | (s,c) <- M.toList helpers]])

recordFieldType :: Shape -> Expression -> Carrier -> Carrier
recordFieldType sh receiver = mapCarrier (instantiate [Project receiver f | c <- variants sh,(f,_) <- payload c])

-- Construct an explicit schema extent from a checked nonrecursive family.
-- Enumeration uses only supplied type/family extents and admitted finite
-- constructors. Fixed constructor indices recover payloads (notably refl);
-- remaining equations filter the complete values, without erasing evidence.
buildSchema :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes -> [(Carrier,Expression)] -> Value
  -> Either Refusal (Carrier,Expression)
buildSchema inv finite helpers shapes env term = do
  schema <- carrierIn inv finite helpers shapes env (get "schemaType" term)
  (binding,captures) <- owner schema
  bindingShape <- lookupShape binding
  unless (schemaExtent bindingShape) (refuse Semantics "Computed schema result is not a schema binding")
  row <- lookupShape (binding <> ".row")
  con <- single row
  values <- domains 0 env [] (array (get "domains" term)) row con captures
  pure (schema,Construct binding ([(indexField binding i,x) | (i,x) <- zip [0..] captures] ++ [(sequenceField,values)]))
  where
    prefix = string (get "sourceFamily" term) <> ".schema"
    owner (Named s) = Right (s,[])
    owner (Fibre s xs) = Right (s,xs)
    owner _ = refuse Representation "Computed schema requires a named binding"
    lookupShape s = maybe (refuse Representation "Computed schema requires an admitted carrier") Right (M.lookup s shapes)
    single sh = case variants sh of
      [c] | isRecord sh -> Right c
      _ -> refuse Semantics "Computed schema row is not a record"
    domains i context values (d:ds) row con captures = do
      typ <- carrierIn inv finite helpers shapes context d
      enumerate S.empty (prefix <> ".domain" <> T.pack (show i)) typ $ \value ->
        domains (i+1) ((typ,value):context) (values ++ [value]) ds row con captures
    domains _ context values [] row con captures = do
      typ <- carrierIn inv finite helpers shapes context (get "memberType" term)
      enumerate S.empty (prefix <> ".payload") typ $ \value ->
        pure (Construct (shapeSymbol row) (construction Nothing row con (captures ++ values ++ [value])))
    guardEquations equations value = foldr (\(a,b) body -> if normalize a == normalize b then body
      else Conditional (Equal a b) body Absent) value equations
    collect name typ values use = do
      body <- use (Iterator name typ)
      pure (Collect name typ values body)
    enumerate _ name (TypeParameter slot) use = collect name AnyValue (Extent (parameterName slot)) use
    enumerate _ _ Boolean use = Sequence <$> traverse (use . Literal) [False,True]
    enumerate seen name typ use = do
      (symbol,indices) <- owner typ
      case M.lookup symbol finite of
        Just domain -> Sequence <$> traverse (use . Enumeration symbol) (F.constructors domain)
        Nothing -> do
          sh <- lookupShape symbol
          unless (not (S.member symbol seen) && null (recursivePeers sh) && sequenceElement sh == Nothing)
            (refuse Representation "Computed schema cannot enumerate recursive or sequence payloads")
          unless (length indices == length (indexTypes sh))
            (refuse Semantics "Computed schema member lost its index telescope")
          case (storedSchema sh,relationParameter sh) of
            (Just binding,_) -> do
              bound <- lookupShape binding
              let count = length (indexTypes bound)
                  source = indices !! count
                  expected = take count indices ++ drop (count+1) indices
                  row = binding <> ".row"
              collect name (Named row) (Project source sequenceField) $ \value -> do
                result <- use (Construct symbol ([(indexField symbol i,x) | (i,x) <- zip [0..] indices]
                  ++ [(familyValue symbol,Project value (familyValue row))]))
                pure (guardEquations [(Project value (indexField row i),x) | (i,x) <- zip [0..] expected] result)
            (_,Just slot) -> do
              let row = familyRow symbol
              collect name (Named row) (Extent (familyName slot)) $ \value -> do
                result <- use (Construct symbol ([(indexField symbol i,x) | (i,x) <- zip [0..] indices]
                  ++ [(familyValue symbol,Project value (familyValue row))]))
                pure (guardEquations [(Project value (indexField row i),x) | (i,x) <- zip [0..] indices] result)
            _ -> Sequence <$> traverse (constructor sh indices) (zip [0 :: Int ..] (variants sh))
      where
        constructor sh indices (ordinal,con) = fields 0 [] (payload con)
          where
            known = M.fromListWith (\_ old -> old) [(i,value) | (Input i,value) <- zip (resultIndices con) indices]
            fields _ values [] = do
              result <- use (Construct (shapeSymbol sh) (construction Nothing sh con values))
              pure (guardEquations (zip (map (instantiate values) (resultIndices con)) indices) result)
            fields i values ((_,domain):rest) = case M.lookup i known of
              Just value -> fields (i+1) (values ++ [value]) rest
              Nothing -> enumerate (S.insert (shapeSymbol sh) seen)
                (name <> ".constructor" <> T.pack (show ordinal) <> ".field" <> T.pack (show i))
                (mapCarrier (instantiate values) domain) $ \value -> fields (i+1) (values ++ [value]) rest

familyCarrier :: Shape -> [Expression] -> Carrier
familyCarrier sh xs = if null (indexTypes sh) then Named (shapeSymbol sh) else Fibre (shapeSymbol sh) xs

indexField :: Text -> Int -> Text
indexField s i = s <> ".index" <> T.pack (show i)

-- A monotone admission pass resolves nested products/sums in dependency order.
-- Cycles are never provisionally accepted, so recursive carriers stay explicit.
-- Family indices are data attributes. A stored callback has a ref-calc rule,
-- but function identity as an index needs its own representation and equality.
dataIndices :: [Carrier] -> Either Refusal ()
dataIndices = mapM_ $ \t -> case t of
  Callable{} -> refuse Representation "Function-valued family indices require a separate representation rule"
  _ -> pure ()

contextualPositions :: Value -> [Int]
contextualPositions d = [round n | Number n <- array (get "nativeContextIndices" d)]

virtualFields :: Shape -> Constructor -> [Text]
virtualFields sh con = [f | i <- contextIndices sh, Input slot <- take 1 (drop i (resultIndices con))
  ,(f,Callable{}):_ <- [drop slot (payload con)]]

contextFields :: Shape -> [Expression] -> Constructor -> [(Text,Expression)]
contextFields sh xs con = [(f,value) | i <- contextIndices sh
  ,Input slot <- take 1 (drop i (resultIndices con)),(f,_):_ <- [drop slot (payload con)]
  ,value <- take 1 (drop i xs)]

storedFields :: Shape -> Constructor -> [(Text,Carrier)]
storedFields sh con = filter ((`notElem` virtualFields sh con) . fst) (payload con)

discover :: Inventory -> M.Map Text F.Domain -> (Shapes,M.Map Text Refusal)
discover inv finite = go M.empty candidates
  where
    initialHelpers = finiteHelpers inv finite
    candidates = M.filterWithKey (\s d -> get "nativeFamily" d /= Null || get "nativeSchema" d /= Null || (S.member (s,"structure") (required inv)
      && get "kind" d `elem` [String "record",String "datatype"]
      && not (get "kind" d == String "datatype" && S.member (s,"behavior") (required inv))
      && s /= builtin inv "bool" && s /= builtin inv "nat" && not (M.member s finite))) (declarations inv)
    header helpers accepted d = do
      unless (get "kind" d == String "datatype" && get "parameters" d == Number 0) (refuse Representation "No provisional datatype header")
      ty <- field inv "type" d
      (args,_,out) <- typedTelescope inv finite helpers accepted ty
      dataIndices [t | (i,t) <- zip [0..] args,i `notElem` contextualPositions d]
      unless (get "tag" (get "term" out) == String "sort") (refuse Representation "Invalid datatype header")
      pure ((Shape (string (get "name" d)) False [] args) {typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d,contextIndices = contextualPositions d})
    deps sh = S.fromList [s | t <- indexTypes sh ++ case sequenceElement sh of
        Just element -> [element]
        Nothing -> [t | c <- variants sh,(_,t) <- payload c]
      ,s <- carrierDependencies t]
    carrierDependencies (Callable a b) = concatMap carrierDependencies (b:a)
    carrierDependencies (Named s) = [s]
    carrierDependencies (Fibre s _) = [s]
    carrierDependencies _ = []
    close accepted table = let next = M.filter (\sh -> deps sh `S.isSubsetOf` (M.keysSet accepted `S.union` M.keysSet table `S.union` M.keysSet finite)) table
      in if M.keysSet next == M.keysSet table then table else close accepted next
    go accepted pending = let
      helpers = indexHelpers inv finite accepted initialHelpers
      headers = M.mapMaybe (either (const Nothing) Just . header helpers accepted) pending
      attempts = M.map (shape inv finite helpers (M.union accepted headers)) pending
      parsed = close accepted (M.mapMaybe (either (const Nothing) Just) attempts)
      components = stronglyConnComp [(sh,s,S.toList (deps sh)) | (s,sh) <- M.toList parsed]
      checked (AcyclicSCC sh) = Right [sh]
      checked (CyclicSCC component) = do
        -- A list nested in a recursive datatype cannot use the sequence
        -- encoding's independent finiteness rule. Its checked nil/cons
        -- constructors already form an ordinary inductive sum; include them
        -- in the component's existing finite node-count representation.
        let shapes' = map recursiveList component
        unless (all (\sh -> null (contextIndices sh) && not (isRecord sh) && sequenceElement sh == Nothing
          && maybe False (inductiveChecked inv) (M.lookup (shapeSymbol sh) (declarations inv))) shapes')
          (refuse Semantics "Recursive carrier component lacks safe inductive positivity evidence")
        let peers = map shapeSymbol shapes'
        unless (null [s | sh <- shapes',c <- variants sh,(_,Callable a b) <- payload c
          ,s <- concatMap carrierDependencies (b:a),s `elem` peers])
          (refuse Representation "Recursive carrier through a callable requires a separate well-foundedness rule")
        pure [sh {recursivePeers = peers} | sh <- shapes']
      recursiveList sh
        | Just _ <- sequenceElement sh
        , Just d <- M.lookup (shapeSymbol sh) (declarations inv)
        , get "nativeSequence" d /= Null =
            sh {sequenceElement = Nothing,familyParameters = Specialize.nativeFamilies d}
        | otherwise = sh
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
shape inv finite helpers shapes d | get "nativeSchema" d /= Null = do
  (captures,context) <- foldM (\(prior,env) ty -> do
    domain <- carrierIn inv finite helpers shapes env ty
    pure (prior ++ [domain],(domain,Input (length prior)):env)) ([],[]) (array (get "schemaCaptures" d))
  (domains,_) <- foldM (\(prior,env) ty -> do
    domain <- carrierIn inv finite helpers shapes env ty
    pure (prior ++ [domain],(domain,Input (length captures + length prior)):env))
    ([],context) (array (get "schemaDomains" d))
  dataIndices (captures ++ domains)
  let symbol = string (get "name" d)
      binding = string (get "schemaBinding" d)
      row = binding <> ".row"
      indices = map Input [0..length captures-1]
      atCaptures owner = if null captures then Named owner else Fibre owner indices
      memberDomain = mapCarrier (mapExpression (\e -> case e of
        Input i | i >= length captures -> Just (Input (i+1))
        _ -> Nothing))
      sh = case string (get "nativeSchema" d) of
        "binding" -> (Shape symbol True [] captures) {sequenceElement = Just (atCaptures row),schemaExtent = True}
        "row" -> Shape symbol True [Constructor (symbol <> ".row")
          ([(symbol <> ".capture" <> T.pack (show i),t) | (i,t) <- zip [0..] captures]
            ++ [(indexField symbol (i+length captures),t) | (i,t) <- zip [0..] domains]
            ++ [(familyValue symbol,AnyValue)]) indices] captures
        _ -> (Shape symbol True [Constructor (symbol <> ".member") [(familyValue symbol,AnyValue)] []]
          (captures ++ [atCaptures binding] ++ map memberDomain domains)) {storedSchema = Just binding}
  pure (sh {typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d})
shape inv finite helpers shapes d | get "nativeFamily" d /= Null = do
  slot <- integer (get "nativeFamily" d)
  (domains,_) <- foldM (\(prior,env) ty -> do
    domain <- carrierIn inv finite helpers shapes env ty
    pure (prior ++ [domain],(domain,Input (length prior)):env))
    ([],[]) (array (get "familyDomains" d))
  dataIndices domains
  let symbol = string (get "name" d)
      member = Shape symbol True [Constructor (symbol <> ".member") [(familyValue symbol,AnyValue)] []] domains
  pure (member {typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d,relationParameter = Just slot})
shape inv finite helpers shapes d | get "nativeSequence" d /= Null = do
  element <- carrierIn inv finite helpers shapes [] (get "nativeSequence" d)
  case element of
    Callable{} -> refuse Representation "Sequences of callables require a separate representation rule"
    _ -> pure ()
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
  let contexts = contextualPositions d
  unless (all (\i -> i >= 0 && i < length familyArgs && case familyArgs !! i of Callable{} -> True; _ -> False) contexts)
    (refuse Syntax "Invalid contextual family parameter")
  dataIndices [t | (i,t) <- zip [0..] familyArgs,i `notElem` contexts]
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
    else do
      checked <- field inv "constructors" d
      case checked of
        Array _ -> pure (map string (array checked))
        _ -> refuse Syntax "Missing checked constructor coverage"
  unless (length cs == S.size (S.fromList cs)) $
    refuse Semantics "Algebraic carrier requires distinct constructor coverage"
  unless (not (null cs) || inductiveChecked inv d) $
    refuse Semantics "Empty carrier requires checked inductive datatype evidence"
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
        candidate = (Shape s record [con] familyArgs) {contextIndices = contexts}
    unless (length (virtualFields candidate con) == length contexts
      && all (\i -> case drop i indices of Input slot:_ -> slot == i; _ -> False) contexts)
      (refuse Semantics "Context parameters must be distinct leading constructor bindings")
    unless (null contexts || all (\(_,typ) -> case typ of Callable{} -> False; _ -> True) (storedFields candidate con))
      (refuse Representation "Stored callbacks with contextual member contracts require a separate binding rule")
    if record then mapM_ (checkProjection candidate) (zip names types) else pure ()
    pure con
  pure ((Shape s record constructors familyArgs) {typeParameters = Specialize.nativeParameters d,familyParameters = Specialize.nativeFamilies d,contextIndices = contexts})
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

-- A theorem statement is lowered from its checked type, independently of its
-- proof body. Proof-valued inputs remain ordinary, constrained domain values.
data EqualityStatement = EqualityStatement
  { statementCalculation :: Calculation, statementDomain :: Carrier } deriving (Eq,Show)

equalityStatements :: Inventory -> M.Map Text F.Domain -> Shapes
  -> M.Map Text (Either Refusal Calculation) -> M.Map Text (Either Refusal EqualityStatement)
equalityStatements inv finite shapes results = M.map (equalityStatement inv finite helpers shapes results)
  (M.filter ((== String "native-equality-statement") . get "kind") (declarations inv))
  -- Statements are checked after calculation admission. Unlike shape discovery,
  -- they may refer to any fully admitted calculation (including unindexed safe
  -- recursion), without using its body to justify admission of its own carrier.
  where helpers = M.union (M.mapMaybe (either (const Nothing) Just) results)
          (indexHelpers inv finite shapes (finiteHelpers inv finite))

equalityStatement :: Inventory -> M.Map Text F.Domain -> Helpers -> Shapes
  -> M.Map Text (Either Refusal Calculation) -> Value -> Either Refusal EqualityStatement
equalityStatement inv finite helpers shapes results d = do
  unless (get "kind" d == String "native-equality-statement")
    (refuse Syntax "Statement lacks checked equality preparation")
  ty <- field inv "type" d
  (ins,env,out) <- typedTelescope inv finite helpers shapes ty
  resultType <- carrierIn inv finite helpers shapes env out
  (symbol,values) <- case resultType of
    Fibre s xs | length xs >= 2 -> Right (s,xs)
    _ -> refuse Representation "Statement result is not an admitted equality family"
  eq <- maybe (refuse Syntax "Missing checked equality carrier") Right (M.lookup symbol (declarations inv))
  unless (not (T.null (builtin inv "equality")) &&
    (symbol == builtin inv "equality" || get "specializationOrigin" eq == String (builtin inv "equality")))
    (refuse Semantics "Statement result is not Agda's registered equality")
  sh <- maybe (refuse Representation "Equality carrier is not admitted") Right (M.lookup symbol shapes)
  domain <- at (length values-2) (indexTypes sh)
  left <- at (length values-2) values
  right <- at (length values-1) values
  let c = Calculation (string (get "name" d)) ins Boolean
        (located "native.equality-statement" out Null (Equal left right)) []
      admitted = M.keysSet (M.mapMaybe (either (const Nothing) Just) results)
  unless (dependencies c `S.isSubsetOf` admitted)
    (refuse Representation "Statement depends on an untranslated calculation")
  pure (EqualityStatement c (mapCarrier (instantiate values) domain))

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
-- unindexed recursion needs a structural concatenation or mapping certificate.
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
      Nothing | mappingCertificate shapes c || checked [c] -> [(calculationSymbol c,c)]
              | otherwise -> []
    select (CyclicSCC cs) | checked cs = [(calculationSymbol c,c) | c <- cs]
                        | otherwise = []
    checked = all (\c -> any indexed (result c : inputs c)
      && maybe False (terminationChecked inv) (M.lookup (calculationSymbol c) (declarations inv)))
    indexed Fibre{} = True
    indexed _ = False
    close table = let next = M.filter (\c -> dependencies c `S.isSubsetOf` M.keysSet table) table
      in if M.keysSet next == M.keysSet table then table else close next

concatenationNormalForm :: Shapes -> Calculation -> Maybe Expression
concatenationNormalForm shapes calc = case (inputs calc,result calc) of
  ([Named first,Named second],Named output) | first == second && second == output -> do
    sh <- M.lookup output shapes
    element <- if schemaExtent sh then Nothing else sequenceElement sh
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

-- A list map/filter has one recursive tail in each nonempty result branch.
-- Other arguments are invariant across recursion. Branches and output elements
-- may inspect the head and those arguments, but never the unconsumed list.
-- Keep the original recursive body: known constructor branches reduce once;
-- calls on unknown lists remain opaque, without an injectivity assumption.
mappingCertificate :: Shapes -> Calculation -> Bool
mappingCertificate shapes calc = or [certify position source | (position,Named source) <- zip [0..] (inputs calc)]
  where
    certify position source = case (result calc,normalize (body calc)) of
      (Named target,Conditional test empty step)
        | Just sourceShape <- M.lookup source shapes,Just targetShape <- M.lookup target shapes
        ,not (schemaExtent sourceShape || schemaExtent targetShape)
        ,Just element <- sequenceElement sourceShape,Just _ <- sequenceElement targetShape ->
          let items = Project (Input position) sequenceField
              headValue = SequenceHead element items
              headOnly value =
                let detached = mapExpression (\e -> if e == headValue then Just Absent else Nothing) value
                    eraseList = mapExpression (\e -> if e == Input position then Just Absent else Nothing)
                in eraseList detached == detached && S.notMember (calculationSymbol calc) (calls value)
              recursive = Call (calculationSymbol calc)
                [if i == position then Construct source [(sequenceField,SequenceOp "tail" items)] else Input i
                | i <- [0..length (inputs calc)-1]]
              branch value | value == recursive = True
              branch (Construct owner [(field,Sequence [value,rest])]) =
                owner == target && field == sequenceField && headOnly value
                && rest == Project recursive sequenceField
              branch (Conditional condition yes no) = headOnly condition && branch yes && branch no
              branch _ = False
          in test == Equal (SequenceOp "isEmpty" items) (Literal True)
            && empty == Construct target [(sequenceField,Sequence [])]
            && branch step
      _ -> False

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
  (map carrierCalls (result calc : inputs calc))
  `S.union` S.unions [calls left `S.union` calls right | (_,left,right) <- staticIndexEquations calc]
  where
    carrierCalls (Fibre _ xs) = S.unions (map calls xs)
    carrierCalls (Callable a b) = S.unions (map carrierCalls (b:a))
    carrierCalls _ = S.empty

calls :: Expression -> S.Set Text
calls (Apply f x) = S.unions (map calls (f:x))
calls (Call s args) = S.insert s (S.unions (map calls args))
calls (Construct _ fields) = S.unions (map (calls . snd) fields)
calls (Project x _) = calls x
calls (Equal x y) = calls x `S.union` calls y
calls (Numeric _ x y) = calls x `S.union` calls y
calls (Sequence xs) = S.unions (map calls xs)
calls (SequenceOp _ xs) = calls xs
calls (SequenceHead _ xs) = calls xs
calls (Collect _ _ xs value) = calls xs `S.union` calls value
calls (Cast _ value) = calls value
calls (Lambda _ _ body) = calls body
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
      unless (maybe True (null . contextIndices) (M.lookup owner shapes))
        (refuse Representation "Context-dependent projection requires its receiver refinement")
      unless (ins == [Named owner] && out == typ) (refuse Syntax "Proper projection signature mismatch")
      pure (Project (Input 0) s)
    Nothing -> do
      tree <- field inv "compiled" d
      unless (length (array (get "sourceSyntax" d)) == 1
        || (get "withParent" d /= Null && M.member (string (get "withParent" d)) (declarations inv))
        || get "extendedLambda" d == Bool True
        || (get "moduleInstanceCopy" d == Bool True && terminationChecked inv d
          && get "tag" tree == String "done" && get "tag" (get "body" tree) == String "definition"))
        (refuse Syntax "No uniquely anchored source definition or checked generated helper")
      p <- field inv "projection" d
      dropped <- if p == Null then Right 0 else subtract 1 <$> integer (get "index" p)
      unless (dropped >= 0 && dropped <= length ins)
        (refuse Representation "Unsupported omitted runtime indices")
      lower Nothing [(left,right) | (_,left,right) <- equations] out (drop dropped (zip ins (map Input [0..]))) tree
  pure (Calculation s ins out lowered equations)
  where
    constructors = constructorTable shapes
    projections = projectionTable shapes
    -- Earlier equations can expose a projection redex around a later fact.
    -- Normalize between substitutions so nested splits still share that fact;
    -- retain the finite, ordered pass rather than iterating equations to a fixpoint.
    rewrite equations = foldl (\f (left,right) ->
      mapExpression (\x -> if x == normalize left then Just right else Nothing) . normalize . f) id equations
    reduce equations = expandWith (rewrite equations) helpers
    schemaContext equations = map (\(typ,value) -> (mapCarrier (reduce equations) typ,reduce equations value))
    requireType equations expected (actual,expr) = if sameCarrier actual expected
      then Right expr else refuse Semantics ("Expression carrier mismatch: expected " <> describe (canonical expected)
        <> "; actual " <> describe (canonical actual))
      where sameCarrier (Callable xs y) (Callable as b) = length xs == length as
              && and (zipWith sameCarrier xs as) && sameCarrier y b
            sameCarrier (Fibre a xs) (Fibre b ys)
              | a == b, Just sh <- M.lookup a shapes
              ,length xs == length (indexTypes sh),length xs == length ys =
                and [sameIndex S.empty (mapCarrier (instantiate (take i xs)) domain) x y
                    | (i,(domain,(x,y))) <- zip [0..] (zip (indexTypes sh) (zip xs ys))]
            sameCarrier a b = canonical a == canonical b
            -- A known constructor is equal to its complete reconstruction.
            -- Compare every active payload, using its dependent domain; no
            -- equality of opaque calls or of unknown constructor tags follows.
            sameIndex seen domain x y
              | left == right = True
              | Just owner <- ownerOf domain,S.notMember owner seen
              ,Just sh <- M.lookup owner shapes,not (schemaExtent sh),Just element <- sequenceElement sh
              ,Sequence xs <- reduce equations (Project (reduce equations x) sequenceField)
              ,Sequence ys <- reduce equations (Project (reduce equations y) sequenceField)
              ,length xs == length ys =
                and [if sequenceSplice a || sequenceSplice b
                  then sequenceIdentity shapes helpers a == sequenceIdentity shapes helpers b
                  else sameIndex (S.insert owner seen) element a b | (a,b) <- zip xs ys]
              | Just owner <- ownerOf domain, S.notMember owner seen
              ,Just sh <- M.lookup owner shapes,not (schemaExtent sh)
              ,Just con <- knownConstructor sh left right =
                let values = [reduce equations (Project left f) | (f,_) <- payload con]
                in and [sameIndex (S.insert owner seen) (mapCarrier (instantiate values) typ)
                     (Project left f) (Project right f) | (f,typ) <- payload con]
              | otherwise = False
              where left = canonicalIndex domain x; right = canonicalIndex domain y
            ownerOf (Named s) = Just s
            ownerOf (Fibre s _) = Just s
            ownerOf _ = Nothing
            knownConstructor sh left right
              | isRecord sh = case variants sh of [con] -> Just con; _ -> Nothing
              | Enumeration a x <- reduce equations (Project left tagField)
              ,Enumeration b y <- reduce equations (Project right tagField)
              ,a == tagType (shapeSymbol sh),a == b,x == y =
                case filter ((== x) . constructorSymbol) (variants sh) of [con] -> Just con; _ -> Nothing
              | otherwise = Nothing
            canonical (Fibre family indices) = case M.lookup family shapes of
              Just sh -> Fibre family [canonicalIndex domain index | (domain,index) <- zip (indexTypes sh) indices]
              Nothing -> mapCarrier (reduce equations) (Fibre family indices)
            canonical typ = typ
            canonicalIndex domain value = let expanded = reduce equations value in case domain of
              Named owner | Just sh <- M.lookup owner shapes, Just _ <- sequenceElement sh,not (schemaExtent sh) ->
                sequenceIdentity shapes helpers (Project expanded sequenceField)
              _ -> sequenceIdentity shapes helpers expanded
            describe (Fibre s xs) = s <> "[" <> T.intercalate "," (map (renderWith id (T.pack . show)) xs) <> "]"
            describe (Callable xs y) = "(" <> T.intercalate ", " (map describe xs) <> ") -> " <> describe y
            describe t = T.pack (show t)
    lower inherited equationsInScope out env tree = fmap (located "native.algebraic-case" tree
      (object ["bindings" .= [renderWith id (T.pack . show) x | (_,x) <- env]
        ,"equations" .= [(renderWith id (T.pack . show) a,renderWith id (T.pack . show) b) | (a,b) <- equationsInScope]])) $ case string (get "tag" tree) of
      "absurd" -> do
        unless (length (array (get "binders" tree)) == length env) (refuse Syntax "Absurd leaf binder count mismatch")
        let impossible = any (uncurry (emptyValue equationsInScope S.empty)) env
        unless impossible (refuse Semantics "Absurd branch has no established empty index fibre")
        pure Absent
      "done" -> do
        unless (length (array (get "binders" tree)) == length env) (refuse Syntax "Case leaf binder count mismatch")
        expressionExpected (Just out) equationsInScope (reverse env) (get "body" tree) >>= requireType equationsInScope out
      "native-schema-case" -> do
        i <- integer (get "position" tree)
        (stored,value) <- at i env
        symbol <- case stored of Fibre s _ -> Right s; _ -> refuse Semantics "Computed schema case lacks membership indices"
        sh <- maybe (refuse Representation "Computed schema case lacks a carrier") Right (M.lookup symbol shapes)
        unless (storedSchema sh /= Nothing) (refuse Semantics "Computed schema case requires a stored-family member")
        concrete <- carrierIn inv finite helpers shapes (schemaContext equationsInScope (reverse env)) (get "memberType" tree)
        -- SysML casts check the nominal carrier. Keep dependent refinements
        -- in the typing context, not in the identity of this value expression.
        castType <- case concrete of
          Named s -> Right s
          Fibre s _ -> Right s
          _ -> refuse Semantics "Computed schema case requires a concrete record carrier"
        lower inherited equationsInScope out
          (take i env ++ [(concrete,Cast castType (Project value (familyValue symbol)))] ++ drop (i+1) env) (get "tree" tree)
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
          refuse Semantics ("Constructor branches are not exhaustive and distinct: expected "
            <> T.pack (show (map fst options)) <> "; present " <> T.pack (show names))
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
          let context f = case typ of
                Fibre owner xs | Just sh <- M.lookup owner shapes
                  ,con:_ <- filter ((== c) . constructorSymbol) (variants sh) -> lookup f (contextFields sh xs con)
                _ -> Nothing
              project f = located "native.case-payload" tree
                (object ["constructor" .= c,"field" .= f,"argument" .= i])
                (case context f of
                  Just value -> value
                  Nothing -> case typ of
                    Natural -> Numeric "monus" selected (NumberLiteral 1)
                    Named owner | Just sh <- M.lookup owner shapes, Just element <- sequenceElement sh ->
                      if any ((== f) . fst) (take 1 fields) then SequenceHead element (Project selected sequenceField)
                      else Construct owner [(sequenceField,SequenceOp "tail" (Project selected sequenceField))]
                    _ -> Project selected f)
              fieldValues = [project f | (f,_) <- allFields]
              expanded = take i env ++ [(mapCarrier (instantiate fieldValues) t,project f) | (f,t) <- fields] ++ drop (i+1) env
          equations <- branchEquations equationsInScope typ selected c
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
    -- A record value requires every field. Descend only through checked records;
    -- revisiting a carrier supplies no evidence that its recursive fields are empty.
    emptyValue equations seen rawType value =
      let typ = mapCarrier (reduce equations) rawType
      in case alternatives equations typ value of
        Right [] -> True
        Right [(c,_)] | Just (owner,xs) <- emptyRecordOwner typ
          , S.notMember owner seen, Just sh <- M.lookup owner shapes, isRecord sh
          , [con] <- filter ((== c) . constructorSymbol) (variants sh)
          , Right facts <- branchEquations equations typ value c ->
            let fields = [(f,maybe (Project value f) id (lookup f (contextFields sh xs con)))
                         | (f,_) <- payload con]
                values = map snd fields
                scope = [(rewrite facts left,rewrite facts right) | (left,right) <- equations] ++ facts
            in any (\((_,fieldType),(_,fieldValue)) ->
                 emptyValue scope (S.insert owner seen)
                   (mapCarrier (instantiate values) fieldType) fieldValue)
               (zip (payload con) fields)
        _ -> False
    emptyRecordOwner (Named owner) = Just (owner,[])
    emptyRecordOwner (Fibre owner xs) = Just (owner,xs)
    emptyRecordOwner _ = Nothing
    alternatives _ Callable{} _ = refuse Semantics "Cannot pattern match a callable input"
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
      unless (not (schemaExtent sh)) (refuse Semantics "Cannot inspect constructors of a schema binding")
      pure [(constructorSymbol c,payload c) | c <- variants sh,compatible equations (indexTypes sh) indices (endpointsFor sh indices selected c)]
    alternatives equations (Named s) selected = case M.lookup s shapes of
      Just sh | schemaExtent sh -> refuse Semantics "Cannot inspect constructors of a schema binding"
      Just sh | not (null (contextIndices sh)) -> refuse Representation "Contextual carrier lacks its membership context"
      Just sh -> let options = [(constructorSymbol c,payload c) | c <- variants sh]
        in Right $ case (sequenceElement sh,normalize (reduce equations (Project selected sequenceField))) of
          (Just _,Sequence []) -> take 1 options
          (Just _,Sequence (_:_)) -> drop 1 options
          _ | not (isRecord sh), Enumeration owner tag <- normalize (reduce equations (Project selected tagField))
              , owner == tagType s -> filter ((== tag) . fst) options
            | otherwise -> options
      Nothing -> maybe (refuse Representation "Missing case carrier") (Right . map (,[]) . F.constructors) (M.lookup s finite)
    endpointsFor sh xs selected c = map (instantiate [maybe (Project selected f) id (lookup f (contextFields sh xs c)) | (f,_) <- payload c]) (resultIndices c)
    distinct (Literal a) (Literal b) = a /= b
    distinct (Enumeration a x) (Enumeration b y) = a /= b || x /= y
    distinct (NumberLiteral a) (NumberLiteral b) = a /= b
    distinct (NumberLiteral 0) (Numeric "+" _ (NumberLiteral k)) = k > 0
    distinct (Numeric "+" _ (NumberLiteral k)) (NumberLiteral 0) = k > 0
    distinct (Construct s [(f,Sequence xs)]) (Construct t [(g,Sequence ys)])
      | s == t && f == sequenceField && g == sequenceField =
          let (lo,hi) = sequenceBounds xs; (lo',hi') = sequenceBounds ys
          in maybe False (< lo') hi || maybe False (< lo) hi'
    distinct _ _ = False
    -- A constructor contributes one element; a residual sequence contributes
    -- an unknown nonnegative number. This separates singleton and at-least-two
    -- fibres without guessing the length of an unresolved tail.
    sequenceBounds xs = (length (filter (not . sequenceSplice) xs),
      if any sequenceSplice xs then Nothing else Just (length xs))
    sequenceSplice (Project _ field) = field == sequenceField
    sequenceSplice (SequenceOp "tail" _) = True
    sequenceSplice _ = False
    compatible equations domains xs ys = length xs == length ys && length domains == length xs
      && not (or (zipWith3 (separated S.empty) domains xs ys))
      where
        reduced = normalize . reduce equations
        separated seen domain x y = distinct (reduced x) (reduced y) || case ownerOf domain >>= (`M.lookup` shapes) of
          Just sh | Just element <- sequenceElement sh,not (schemaExtent sh)
            ,S.notMember (shapeSymbol sh) seen ->
              let prefix value = case reduced (Project value sequenceField) of
                    Sequence values -> takeWhile (not . sequenceSplice) values
                    _ -> []
              in or (zipWith (separated (S.insert (shapeSymbol sh) seen) element) (prefix x) (prefix y))
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
    branchEquations scope (Fibre s xs) selected c = do
      sh <- maybe (refuse Representation "Missing family") Right (M.lookup s shapes)
      con <- case filter ((== c) . constructorSymbol) (variants sh) of
        [v] -> Right v
        _ -> refuse Representation "Missing family branch"
      -- Only replace symbolic references. Constants are never rewritten.
      let tagFact = [(Project selected tagField,Enumeration (tagType s) c)
            | not (isRecord sh),sequenceElement sh == Nothing]
      -- Shared constructor payloads relate all their occurrences. For refl,
      -- both endpoints equal one payload: use the first equation when solving
      -- the second, rather than recording two competing rewrites of the same
      -- field and losing the equality between the endpoints.
      let solved = foldl (\facts (left,right) -> facts ++ orient
            (reduce (scope ++ facts) left,reduce (scope ++ facts) right)) tagFact
            (zip xs (endpointsFor sh xs selected con))
      pure solved
      where
        orient (Numeric "+" x (NumberLiteral a),Numeric "+" y (NumberLiteral b)) | a == b = orient (x,y)
        orient (NumberLiteral a,Numeric "+" y (NumberLiteral b)) | a >= b = orient (NumberLiteral (a-b),y)
        orient (Numeric "+" x (NumberLiteral a),NumberLiteral b) | b >= a = orient (x,NumberLiteral (b-a))
        orient (Construct s [(f,x)],Construct t [(g,y)])
          | s == t && f == sequenceField && g == sequenceField = orientSequence s (x,y)
        orient (Construct s xs,Construct t ys)
          | s == t, Just sh <- M.lookup s shapes
          , isRecord sh || sameConstructor xs ys
          , map fst xs == map fst ys = concatMap orient (zip (map snd xs) (map snd ys))
        orient (Sequence (x:xs),Sequence (y:ys)) = orient (x,y) ++ orient (Sequence xs,Sequence ys)
        orient (x@Call{},y@Project{}) = [(y,x)]
        orient (x@Project{},y@Call{}) = [(x,y)]
        orient (x,y) | x == y = []
                     | isReference x = [(x,y)]
                     | isReference y = [(y,x)]
                     | otherwise = []
        sameConstructor xs ys = case (lookup tagField xs,lookup tagField ys) of
          (Just (Enumeration a x),Just (Enumeration b y)) -> a == b && x == y
          _ -> False
        orientSequence _ (Sequence [x,Project xs f],Sequence [y,Project ys g])
          | f == sequenceField && g == sequenceField = orient (x,y) ++ orient (xs,ys)
        orientSequence owner (Sequence (x:xs),Sequence [y,Project ys f])
          | f == sequenceField = orient (x,y) ++ orient (Construct owner [(sequenceField,Sequence xs)],ys)
        orientSequence owner (Sequence [x,Project xs f],Sequence (y:ys))
          | f == sequenceField = orient (x,y) ++ orient (xs,Construct owner [(sequenceField,Sequence ys)])
        orientSequence _ values = orient values
    branchEquations _ Boolean selected c = Right [(selected,Literal (c == builtin inv "true"))]
    branchEquations _ Natural selected c | c == builtin inv "zero" = Right [(selected,NumberLiteral 0)]
    branchEquations _ Natural selected c | c == builtin inv "suc" =
      Right [(Numeric "+" (Numeric "monus" selected (NumberLiteral 1)) (NumberLiteral 1),selected)]
    branchEquations _ (Named s) selected c | M.member s finite = Right [(selected,Enumeration s c)]
    branchEquations _ (Named s) selected c | Just sh <- M.lookup s shapes, Just element <- sequenceElement sh =
      Right $ case variants sh of
       [nil,cons] | c == constructorSymbol nil ->
        -- Dependent types may already contain the normalized contents of a
        -- list wrapper (notably a tail). Retain the same empty-branch fact in
        -- both forms so that a nested [] pattern also refines those indices.
        [(selected,Construct s [(sequenceField,Sequence [])])
        ,(normalize (Project selected sequenceField),Sequence [])]
                 | c == constructorSymbol cons ->
        [(selected,Construct s [(sequenceField,Sequence [SequenceHead element (Project selected sequenceField)
          ,SequenceOp "tail" (Project selected sequenceField)])])]
       _ -> case normalize (Project selected sequenceField) of
        Sequence [_,Project tailValue field] | field == sequenceField ->
          [(Construct s [(sequenceField,Project tailValue sequenceField)],tailValue)]
        _ -> []
    branchEquations _ (Named s) selected c | Just sh <- M.lookup s shapes, not (isRecord sh) =
      Right [(Project selected tagField,Enumeration (tagType s) c)]
    branchEquations _ _ _ _ = Right []
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
        Callable{} -> refuse Semantics "Cannot pattern match a callable input"
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
          eliminate = eliminateIn equationsInScope env
      case string (get "tag" term) of
        "native-lambda" -> do
          let types = array (get "inputs" term)
          unless (not (null types)) (refuse Syntax "Malformed native lambda telescope")
          (locals,context) <- foldM (\(locals,context) ty -> do
            domain <- carrierIn inv finite helpers shapes (schemaContext equationsInScope context) ty
            let name = "lambdaArgument" <> T.pack (show (length env + length locals))
            pure (locals ++ [(name,domain)],(domain,Iterator name domain):context)) ([],env) types
          out <- carrierIn inv finite helpers shapes (schemaContext equationsInScope context) (get "result" term)
          value <- expressionExpected (Just out) equationsInScope context (get "body" term) >>= requireType equationsInScope out
          let rebase = mapCarrier (mapExpression (\e -> case e of
                Iterator name _ -> Argument <$> lookup name (zip (map fst locals) [0..])
                _ -> Nothing))
          eliminate (Callable (map (rebase . snd) locals) (rebase out),Lambda locals out value) es
        "native-schema-build" -> buildSchema inv finite helpers shapes (schemaContext equationsInScope env) term
        "native-schema-inject" -> do
          concrete <- carrierIn inv finite helpers shapes (schemaContext equationsInScope env) (get "memberType" term)
          schema <- carrierIn inv finite helpers shapes (schemaContext equationsInScope env) (get "schemaType" term)
          (symbol,indices) <- case schema of Fibre s xs -> Right (s,xs); _ -> refuse Semantics "Schema injection lost its indices"
          sh <- maybe (refuse Representation "Schema injection lacks an admitted carrier") Right (M.lookup symbol shapes)
          unless (storedSchema sh /= Nothing) (refuse Semantics "Schema injection requires stored membership")
          value <- expressionExpected (Just concrete) equationsInScope env (get "value" term) >>= requireType equationsInScope concrete
          pure (schema,Construct symbol ([(indexField symbol i,x) | (i,x) <- zip [0..] indices] ++ [(familyValue symbol,value)]))
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
                        _ -> refuse Representation ("Constructor has no admitted carrier: " <> c)
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
    recover equations = recoverCarrierInputs shapes canonical
      where
        canonical domain value = let expanded = reduce equations (normalize value) in case domain of
          Named owner | Just sh <- M.lookup owner shapes, Just _ <- sequenceElement sh,not (schemaExtent sh) -> sequenceIdentity shapes helpers (Project expanded sequenceField)
          _ -> normalize expanded
    argument equationsInScope env typ a = do
      unless (get "tag" a == String "apply") (refuse Syntax "Constructor argument is not an application")
      expressionExpected (Just typ) equationsInScope env (get "value" (get "argument" a)) >>= requireType equationsInScope typ
    eliminateIn _ _ value [] = Right value
    eliminateIn equations env (Callable domains out,fn) es@(_:_) = do
      unless (length es >= length domains) (refuse Representation "Partial callback application requires runtime closure construction")
      values <- foldM (\prior (domain,e) -> do
        value <- argument equations env (applyCallback prior domain) e
        pure (prior ++ [value])) [] (zip domains es)
      eliminateIn equations env (applyCallback values out,
        located "native.callable-invocation" (toJSON (take (length domains) es)) Null (Apply fn values)) (drop (length domains) es)
    eliminateIn equations env (typ,expr) (e:es) = do
      unless (get "tag" e == String "project") (refuse Syntax "Unsupported value elimination")
      let f = string (get "symbol" e)
      (owner,ft) <- maybe (refuse Representation "Projection has no admitted record") Right (M.lookup f projections)
      unless (recordOwner typ owner) (refuse Semantics "Projection is applied to the wrong record")
      eliminateIn equations env (projectedCarrier shapes typ expr ft,located "native.projection-elimination" e Null (Project expr f)) es

construction :: Maybe Value -> Shape -> Constructor -> [Expression] -> [(Text,Expression)]
construction _ sh _ values | Just _ <- sequenceElement sh = [(sequenceField,case values of
  [] -> Sequence []
  [x,xs] -> Sequence [x,Project xs sequenceField]
  _ -> error "admitted sequence constructor lost its payload arity")]
construction callSite sh con values =
  let supplied = [(f,v) | ((f,_),v) <- zip (payload con) values,f `notElem` virtualFields sh con]
      indices = [(indexField (shapeSymbol sh) i,instantiate values e) | (i,e) <- zip [0..] (resultIndices con),i `notElem` contextIndices sh]
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
      | v <- variants sh,(i,(f,_)) <- zip [0 :: Int ..] (payload v),f `notElem` virtualFields sh v]

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
renderCarrier _ Callable{} = "Calculations::Calculation"
renderCarrier label (Named s) = quote (label s)
renderCarrier label (Fibre s _) = quote (label s)

renderWith :: (Text -> Text) -> (Int -> Text) -> Expression -> Text
renderWith label input = D.render . renderWithDoc label input ""

renderWithDoc :: (Text -> Text) -> (Int -> Text) -> Text -> Expression -> D.Doc
renderWithDoc label input owner = renderParameterizedDoc label input owner (const []) (const []) quote

argumentName :: Int -> Text
argumentName 0 = "argument"
argumentName i = "argument" <> T.pack (show i)

parameterName :: Int -> Text
parameterName i = "typeArgument" <> T.pack (show i)

familyName :: Int -> Text
familyName i = "familyArgument" <> T.pack (show i)
familyRow :: Text -> Text
familyRow s = s <> ".relation-row"
familyValue :: Text -> Text
familyValue s = s <> ".value"
relationRow :: Shape -> Shape
relationRow member = (Shape s True [Constructor (s <> ".row") fields []] [])
  {relationRowOf = Just (shapeSymbol member)}
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
      Extent name -> D.text (parameter name)
      Iterator name typ -> "(" <> D.text (quote name) <> " as " <> D.text (renderCarrier label typ) <> ")"
      Collect name _ xs value -> "(" <> go xs <> ")->collect { in " <> D.text (quote name) <> "; " <> go value <> " }"
      Cast typ value -> "(" <> go value <> " as " <> D.text (quote (label typ)) <> ")"
      Lambda args out value -> "{ "
        <> D.joinDoc " " [D.text ("in " <> quote name <> " : " <> renderCarrier label typ <> " [1];") | (name,typ) <- args]
        <> D.text (" return 'result' : " <> renderCarrier label out <> " [1]; ") <> go value <> " }"
      Argument i -> D.text (quote (argumentName i))
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
      Apply (Project receiver member) value -> D.text (quote (label (callableInvoker member)))
        <> "(" <> D.joinDoc ", " (map go (receiver:value)) <> ")"
      Apply fn values -> go fn <> "(" <> D.joinDoc ", " (map go values) <> ")"
      Absent -> "null"
    evidence e@(Call sym _) = D.derived "native.call-site" [] (object ["callee" .= sym]) [annotation e]
    evidence e@(Project _ fieldName) = D.derived "native.field-access" [] (object ["field" .= fieldName]) [annotation e]
    evidence e = annotation e
    role Call{} = "call"
    role Apply{} = "callback-invocation"
    role Lambda{} = "callback-construction"
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
renderCalculationDoc = renderOperationDoc Nothing

renderStatementDoc :: Inventory -> Shapes -> (Text -> Text) -> EqualityStatement -> D.Doc
renderStatementDoc inv shapes label law =
  renderOperationDoc (Just (statementDomain law)) inv shapes label (statementCalculation law)

renderOperationDoc :: Maybe Carrier -> Inventory -> Shapes -> (Text -> Text) -> Calculation -> D.Doc
renderOperationDoc statement inv shapes label c = D.mark owner (if isStatement then "statement-constraint" else "calculation")
  (D.derived (if isStatement then "native.equality-statement" else "native.calculation") [D.root owner "type"] Null []) $
  D.linesDoc ([D.text ("  " <> (if isStatement then "constraint" else "calc") <> " def " <> quote (label owner) <> " {")]
  ++ [D.text ("    in " <> quote (parameterName i) <> " : Base::Anything [0..*];") | i <- parameters]
  ++ [D.text ("    in " <> quote (familyName i) <> " : " <> quote (label (familyRow s)) <> " [0..*];") | (i,s) <- families]
  ++ concat [renderInput i typ | (i,typ) <- zip [0 :: Int ..] (inputs c)]
  ++ (if isStatement then [] else renderResult)
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
     | (i,condition) <- zip [0 :: Int ..] (calculationContractsIn shapes label c)]
  ++ (if isStatement then ["    " <> statementBody] else []) ++ ["  }"])
  where
    isStatement = case statement of Just _ -> True; Nothing -> False
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
    resultBody = renderParameterizedDoc label input owner calcBindings shapeBindings binding (body c)
    statementBody = case (statement,body c) of
      (Just (Named s),Equal left right) | Just sh <- M.lookup s shapes,Just _ <- sequenceElement sh,not (schemaExtent sh) ->
        D.mark owner "statement-equality" (annotation (body c)) $
          "SequenceFunctions::equals(" <> expression (Project left sequenceField) <> ", "
            <> expression (Project right sequenceField) <> ")"
      _ -> resultBody
    expression = renderParameterizedDoc label input owner calcBindings shapeBindings binding
    renderResult = case result c of
      Callable domain out ->
        ["    return ref calc 'result' [1] = " <> resultBody <> " {"]
        ++ map D.text (callableBody (quote (label owner) <> "::'result'") domain out) ++ ["    }"]
      typ -> [D.text ("    return 'result' : " <> renderCarrier label typ <> " [1] = ") <> resultBody <> ";"]
    renderInput i (Callable domain out) = map D.text $
      ["    in calc " <> quote ("input" <> T.pack (show i)) <> " {"]
      ++ callableBody (input i) domain out ++ ["    }"]
    renderInput i typ = [D.text ("    in " <> quote ("input" <> T.pack (show i)) <> " : " <> renderCarrier label typ <> " [1];")]
    callableBody scope domain out =
      ["      in " <> quote (argumentName i) <> " : " <> renderCarrier label typ <> " [1];" | (i,typ) <- zip [0..] domain]
      ++ ["      return 'result' : " <> renderCarrier label out <> " [1];"]
      ++ ["      assert constraint { " <> condition <> " }"
         | (fieldName,typ) <- [(argumentName i,typ) | (i,typ) <- zip [0..] domain] ++ [("result",out)]
         ,let value = scope <> "::" <> quote fieldName
         ,condition <- parameterRefinements shapes label binding value typ
           ++ refinementTextIn shapes label input binding value typ]


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
  , (i,(domain,x)) <- zip [0..] (zip (indexTypes sh) xs),i `notElem` contextIndices sh]
  ++ contextualRefinements shapes label input binding value s xs
  ++ ["(" <> value <> "." <> quote (label (indexField s i)) <> " == " <> renderIndexIn shapes label input binding x <> ")"
     | (i,x) <- zip [0..] xs, M.notMember s shapes]
refinementTextIn _ _ _ _ _ _ = []

-- A contextual carrier is a domain value plus a membership condition in the
-- caller's scope. Callable bindings are not data indices or stored identities.
contextualRefinements :: Shapes -> (Text -> Text) -> (Int -> Text) -> (Text -> Text) -> Text -> Text -> [Expression] -> [Text]
contextualRefinements shapes label input binding value symbol indices =
  [guarded sh con condition
  | Just sh <- [M.lookup symbol shapes],not (null (contextIndices sh)),con <- variants sh
  ,let contextual = [(f,renderIndexIn shapes label input binding x)
          | i <- contextIndices sh,Input slot <- take 1 (drop i (resultIndices con))
          ,(f,_):_ <- [drop slot (payload con)],x <- take 1 (drop i indices)]
       field f = maybe (value <> "." <> quote (label f)) id (lookup f contextual)
       argument i = field (fst (payload con !! i))
  ,condition <- concat [refinementTextIn shapes label argument binding (field f) typ
                        | (f,typ) <- storedFields sh con]
       ++ [indexEquality shapes label argument binding domain (value <> "." <> quote (label (indexField symbol i))) endpoint
          | (i,(domain,endpoint)) <- zip [0..] (zip (indexTypes sh) (resultIndices con)),i `notElem` contextIndices sh]]
  where
    guarded sh con condition | isRecord sh = condition
      | otherwise = "(if " <> value <> "." <> quote (label tagField) <> " == "
          <> quote (label (tagType symbol)) <> "::" <> quote (label (constructorSymbol con))
          <> " ? " <> condition <> " else true)"

-- Type extents are representation bindings, not elements of a source list.
-- Membership constraints still check them; schema equality retains precisely
-- the ordered, nonunique contents when equal bindings use different orders.
indexEquality :: Shapes -> (Text -> Text) -> (Int -> Text) -> (Text -> Text) -> Carrier -> Text -> Expression -> Text
indexEquality shapes label input binding domain value expected =
  let rendered = renderIndexIn shapes label input binding expected
  in case domain of
    Named s | Just sh <- M.lookup s shapes, Just _ <- sequenceElement sh, not (schemaExtent sh) ->
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
hasValidity sh = storedSchema sh /= Nothing || not (null (familyParameters sh)) || not (null (typeParameters sh)) || not (isRecord sh) || any refined [t | c <- variants sh,(_,t) <- payload c]
  where refined Natural = True
        refined Fibre{} = True
        refined _ = False

-- SysML invocation names must be feature chains, not arbitrary receiver
-- expressions. A typed member helper gives computed receivers a named input
-- while keeping the invocation inside the caller's selected branch.
callableInvoker :: Text -> Text
callableInvoker member = member <> ".invoke"

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
      ] ++ parameterFields sh
      ++ ["    attribute " <> quote (label (indexField (shapeSymbol sh) i)) <> " : " <> renderCarrier label t <> " [1];"
         | (i,t) <- zip [0..] (indexTypes sh),i `notElem` contextIndices sh]
      ++ ["    attribute " <> quote sequenceField <> " : " <> renderCarrier label element
        <> " [0..*]" <> (if schemaExtent sh then ";" else " ordered nonunique;")]
      ++ ["    assert constraint 'finite-sequence' { SequenceFunctions::size(" <> quote sequenceField <> ") < * }" | not (schemaExtent sh)]
      ++ ["    assert constraint { " <> quote sequenceField <> "->forAll { in element; " <> condition <> " } }"
         | let value = case element of
                 Named{} -> "(element as " <> renderCarrier label element <> ")"
                 Fibre{} -> "(element as " <> renderCarrier label element <> ")"
                 _ -> "element"
         ,condition <- refinementTextIn shapes label (\i -> quote (label (indexField (shapeSymbol sh) i))) quote value element
           ++ parameterRefinements shapes label quote value element]
      ++ ["    assert constraint { " <> condition <> " }" | condition <- familyDomainConstraints shapes label quote (familyParameters sh)]
      ++ ["    assert constraint { " <> condition <> " }"
         | schemaExtent sh,(i,domain) <- zip [0..] (indexTypes sh)
         ,let field j = quote (label (indexField (shapeSymbol sh) j))
         ,condition <- refinementTextIn shapes label field quote (field i) domain
           ++ parameterRefinements shapes label quote (field i) domain]
      ++ ["  }"]
    renderShape sh = (if isRecord sh || null (variants sh) then [] else
      ["  enum def " <> quote (label (tagType (shapeSymbol sh))) <> " {"]
      ++ ["    enum " <> quote (label (constructorSymbol c)) <> ";" | c <- variants sh] ++ ["  }"])
      ++ ["  attribute def " <> quote (label (shapeSymbol sh)) <> " {"]
      ++ ["    attribute redefines self : " <> quote (label (shapeSymbol sh)) <> ";"
         ,"    assert constraint 'exact-type' { " <> quote (label (shapeSymbol sh))
           <> "::self hastype " <> quote (label (shapeSymbol sh)) <> " }"]
      ++ parameterFields sh
      ++ ["    attribute " <> quote (label (countField (shapeSymbol sh))) <> " : ScalarValues::Natural [1];" | not (null (recursivePeers sh))]
      ++ (if isRecord sh || null (variants sh) then [] else
        ["    attribute " <> quote (label tagField) <> " : " <> quote (label (tagType (shapeSymbol sh))) <> " [1];"])
      ++ ["    attribute " <> quote (label (indexField (shapeSymbol sh) i)) <> " : " <> renderCarrier label t <> " [1];"
         | (i,t) <- zip [0..] (indexTypes sh),i `notElem` contextIndices sh]
      ++ concat [renderField sh f ty | c <- variants sh,(f,ty) <- storedFields sh c]
      ++ (if not (hasValidity sh) then [] else
        ["    assert constraint 'valid-payload' { " <> quote (label (validitySymbol (shapeSymbol sh)))
          <> "(" <> quote (label (shapeSymbol sh)) <> "::self) }"])
      ++ ["  }"]
      ++ (if not (hasValidity sh) then [] else
        ["  constraint def " <> quote (label (validitySymbol (shapeSymbol sh))) <> " {"
        ,"    in 'value' : " <> quote (label (shapeSymbol sh)) <> " [1];"
        ,"    " <> validity shapes label sh
        ,"  }"])
      ++ concat [renderInvoker sh f a b | c <- variants sh,(f,Callable a b) <- storedFields sh c]
    renderField sh f (Callable domain out) =
      ["    ref calc " <> quote (label f) <> multiplicity sh <> " {"]
      ++ ["      in " <> quote (argumentName i) <> " : " <> renderCarrier label typ <> " [1];" | (i,typ) <- zip [0..] domain]
      ++ ["      return 'result' : " <> renderCarrier label out <> " [1];"]
      ++ ["      assert constraint { " <> condition <> " }"
         | (member,typ) <- [(argumentName i,typ) | (i,typ) <- zip [0..] domain] ++ [("result",out)]
         ,let owner = quote (label (shapeSymbol sh))
              binding p = owner <> "::" <> quote p
              value = owner <> "::" <> quote (label f) <> "::" <> quote member
         ,condition <- parameterRefinements shapes label binding value typ
           ++ refinementTextIn shapes label (\i -> owner <> "::" <> quote (label (fieldAt sh f i))) binding value typ]
      ++ ["    }"]
    renderField sh f ty = ["    attribute " <> quote (label f) <> " : " <> renderCarrier label ty <> multiplicity sh <> ";"]
    multiplicity sh = if isRecord sh then " [1]" else " [0..1]"
    fieldAt sh member i = head [name | c <- variants sh,member `elem` map fst (payload c)
      ,(j,(name,_)) <- zip [0..] (payload c),i == j]
    renderInvoker sh f domain out =
      let scope = quote (label (callableInvoker f))
          receiver = scope <> "::'receiver'"
          arguments = [scope <> "::" <> quote (argumentName i) | i <- [0..length domain-1]]
          returned = scope <> "::'result'"
          binding p = receiver <> "." <> quote p
      in ["  calc def " <> scope <> " {"
         ,"    in 'receiver' : " <> quote (label (shapeSymbol sh)) <> " [1];"
         ] ++ ["    in " <> quote (argumentName i) <> " : " <> renderCarrier label typ <> " [1];" | (i,typ) <- zip [0..] domain]
         ++ ["    return 'result' : " <> renderCarrier label out <> " [1] = "
           <> receiver <> "." <> quote (label f) <> "(" <> T.intercalate ", " arguments <> ");"
         ,"    assert constraint { SequenceFunctions::size(" <> receiver <> "." <> quote (label f) <> ") == 1 }"]
         ++ ["    assert constraint { " <> condition <> " }"
            | (value,typ) <- zip arguments domain ++ [(returned,out)]
            ,condition <- parameterRefinements shapes label binding value typ
              ++ refinementTextIn shapes label (\i -> receiver <> "." <> quote (label (fieldAt sh f i))) binding value typ]
         ++ ["  }"]

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
  ,let rowField j = "(row as " <> quote (label (familyRow symbol)) <> ")." <> quote (label (indexField (familyRow symbol) j))
       field = rowField i
  ,condition <- refinementTextIn shapes label rowField binding field domain
    ++ parameterRefinements shapes label binding field domain]

validity :: Shapes -> (Text -> Text) -> Shape -> Text
validity _ _ sh | not (isRecord sh) && sequenceElement sh == Nothing && null (variants sh) = "false"
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
      | c <- variants sh,(f,_) <- storedFields sh c])
      ++ [guarded c (indexEquality shapes label (\j -> fieldText (fst (payload c !! j))) fieldText domain
           (fieldText (indexField (shapeSymbol sh) i)) e)
         | c <- variants sh,(i,(domain,e)) <- zip [0..] (zip (indexTypes sh) (resultIndices c)),i `notElem` contextIndices sh, null (contextIndices sh)]
      ++ [guarded c constraint | c <- variants sh,(f,t) <- storedFields sh c
         ,constraint <- (if null (contextIndices sh) then refinementTextIn shapes label (\j -> fieldText (fst (payload c !! j))) fieldText (fieldText f) t else [])
           ++ [condition | relationRowOf sh == Nothing
              ,condition <- parameterRefinements shapes label fieldText (fieldText f) t]]
      ++ [condition | (i,t) <- zip [0..] (indexTypes sh)
         ,condition <- parameterRefinements shapes label fieldText (fieldText (indexField (shapeSymbol sh) i)) t
           ++ [condition | storedSchema sh /= Nothing || relationParameter sh /= Nothing
              ,condition <- refinementTextIn shapes label (\j -> fieldText (indexField (shapeSymbol sh) j)) fieldText (fieldText (indexField (shapeSymbol sh) i)) t]]
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
      ++ case storedSchema sh of
        Nothing -> []
        Just binding ->
          let prefix = maybe 0 (length . indexTypes) (M.lookup binding shapes) in
          [fieldText (indexField (shapeSymbol sh) prefix) <> "." <> quote sequenceField <> "->exists { in row; "
            <> T.intercalate " and "
              (["((row as " <> quote (label (binding <> ".row")) <> ")." <> quote (label (indexField (binding <> ".row") i))
                <> " == " <> fieldText (indexField (shapeSymbol sh) (if i < prefix then i else i+1)) <> ")" | i <- [0..length (indexTypes sh)-2]]
              ++ ["((row as " <> quote (label (binding <> ".row")) <> ")." <> quote (label (familyValue (binding <> ".row")))
                <> " == " <> fieldText (familyValue (shapeSymbol sh)) <> ")"])
            <> " }"]

-- All symbols used by the renderer, including generated domain-specific
-- helpers, participate in the common name-collision check.
references :: Shapes -> [Text]
references shapes = concat
  [[shapeSymbol sh] ++ map constructorSymbol (variants sh) ++ concatMap (map fst . payload) (variants sh)
    ++ [callableInvoker f | c <- variants sh,(f,Callable{}) <- payload c]
    ++ [countField (shapeSymbol sh) | not (null (recursivePeers sh))]
    ++ [indexField (shapeSymbol sh) i | i <- [0..length (indexTypes sh)-1]]
    ++ (if hasValidity sh then [validitySymbol (shapeSymbol sh)] else [])
    ++ (if isRecord sh || null (variants sh) then [] else [tagType (shapeSymbol sh),tagField]) | sh <- M.elems shapes]

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
    ++ [(callableInvoker f,(if isRecord sh then display f else display (constructorSymbol c) <> ".payload" <> T.pack (show i)) <> ".invoke")
       | c <- variants sh,(i,(f,Callable{})) <- zip [0 :: Int ..] (payload c)]
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
  ,"kind" .= (if schemaExtent sh then "stored-schema" else case sequenceElement sh of Just _ -> "sequence"; Nothing -> if isRecord sh then "record" else "sum" :: Text)
  ,"storedSchema" .= fmap target (storedSchema sh)
  ,"sequence" .= (case sequenceElement sh of
      Just element -> object ["elementType" .= renderCarrier label element,"ordered" .= not (schemaExtent sh),"unique" .= schemaExtent sh
        ,"itemsTarget" .= (target (shapeSymbol sh) <> "::" <> quote sequenceField),"finite" .= not (schemaExtent sh)]
      Nothing -> Null)
  ,"admissibility" .= (if hasValidity sh then String (target (validitySymbol (shapeSymbol sh))) else Null)
  ,"contextParameters" .= [object ["position" .= i,"representation" .= ("contextual-membership" :: Text)] | i <- contextIndices sh]
  ,"indices" .= [object ["position" .= i,"type" .= renderCarrier label t
    ,"target" .= (target (shapeSymbol sh) <> "::" <> quote (label (indexField (shapeSymbol sh) i)))]
    | (i,t) <- zip [0 :: Int ..] (indexTypes sh),i `notElem` contextIndices sh]
  ,"constructors" .= [object ["symbol" .= constructorSymbol c,"target" .= target (constructorSymbol c)
    ,"resultIndices" .= [renderIndexIn shapes label (\i -> quote (label (fst (payload c !! i)))) quote endpoint
      | (i,endpoint) <- zip [0..] (resultIndices c),i `notElem` contextIndices sh]
    ,"payload" .= [object ["position" .= i,"field" .= f
      ,"type" .= renderCarrier label typ
      ,"refinementScope" .= (if null (contextIndices sh) then "carrier" else "calculation-membership" :: Text)
      ,"refinements" .= (if null (contextIndices sh)
          then refinementTextIn shapes label (\j -> quote (label (fst (payload c !! j)))) quote (quote (label f)) typ
          else [])
      ,"target" .= (case sequenceElement sh of
          Just _ -> Null
          Nothing -> String (target (shapeSymbol sh) <> "::" <> quote (label f)))]
      | (i,(f,typ)) <- zip [0 :: Int ..] (payload c),f `notElem` virtualFields sh c]] | c <- variants sh]] | sh <- M.elems shapes]
  where target s = "AgdaModel::" <> quote (label s)
