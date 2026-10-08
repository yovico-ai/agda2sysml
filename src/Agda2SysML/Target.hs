{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Agda2SysML.Target (generate, Generated(..), Expr(Literal, Input, Conditional), renderExpr, evaluate) where

import qualified Agda2SysML.Derivation as D
import Agda2SysML.Inventory hiding (field)
import Agda2SysML.Diagnostic
import qualified Agda2SysML.FiniteTarget as Finite
import qualified Agda2SysML.RelationTarget as Relation
import qualified Agda2SysML.AlgebraicTarget as Algebraic
import qualified Agda2SysML.Presentation as Presentation
import qualified Agda2SysML.Specialize as Specialize
import Agda2SysML.Sharing (digest)
import qualified Data.Text.Encoding as TE
import Control.Monad (unless)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

data Expr = Annotated D.Origin Expr
  | NLiteral Bool
  | NInput Int
  | NConditional Expr Expr Expr
  deriving Show

unmark :: Expr -> Expr
unmark (Annotated _ x) = unmark x
unmark x = x

instance Eq Expr where
  x == y | NLiteral a0 <- unmark x, NLiteral b0 <- unmark y = a0 == b0
  x == y | NInput a0 <- unmark x, NInput b0 <- unmark y = a0 == b0
  x == y | NConditional a0 a1 a2 <- unmark x, NConditional b0 b1 b2 <- unmark y = a0 == b0 && a1 == b1 && a2 == b2
  _ == _ = False
pattern Literal :: Bool -> Expr
pattern Literal b <- (unmark -> NLiteral b) where Literal b = NLiteral b
pattern Input :: Int -> Expr
pattern Input i <- (unmark -> NInput i) where Input i = NInput i
pattern Conditional :: Expr -> Expr -> Expr -> Expr
pattern Conditional p x y <- (unmark -> NConditional p x y) where Conditional p x y = NConditional p x y
{-# COMPLETE Literal, Input, Conditional #-}

annotation :: Expr -> D.Origin
annotation (Annotated o _) = o
annotation _ = D.generated "native.generated-expression"

located :: Text -> Value -> Value -> Expr -> Expr
-- A fresh root gets its first justified origin here. Existing annotations,
-- including explicit unavailable boundaries, must survive unchanged as premises.
located rule input premises e = Annotated (D.origin rule input premises parents) e
  where parents = case e of Annotated o _ -> [o]; _ -> []

data Calculation = BooleanCalculation Text Int Expr
  | FiniteCalculation Text Finite.Domain Int Finite.Expression
  | AlgebraicCalculation Algebraic.Calculation

calculationSymbol :: Calculation -> Text
calculationSymbol (BooleanCalculation symbol _ _) = symbol
calculationSymbol (FiniteCalculation symbol _ _ _) = symbol
calculationSymbol (AlgebraicCalculation c) = Algebraic.calculationSymbol c

data Generated = Generated
  { modelText :: Text, correspondence :: Value, diagnostics :: [Value], complete :: Bool }

evaluate :: [Bool] -> Expr -> Maybe Bool
evaluate _ (Literal b) = Just b
evaluate env (Input i) = index i env
evaluate env (Conditional test yes no) = do
  b <- evaluate env test
  evaluate env (if b then yes else no)

renderExpr :: Expr -> Text
renderExpr = D.render . renderExprDoc ""

renderExprDoc :: Text -> Expr -> D.Doc
renderExprDoc owner = go
  where
    go e = D.mark owner "boolean-expression" (annotation e) $ case e of
      Literal True -> "true"
      Literal False -> "false"
      Input i -> D.text (quote ("input" <> T.pack (show i)))
      Conditional test yes no -> "(if " <> go test <> " ? " <> go yes <> " else " <> go no <> ")"

quote :: Text -> Text
quote x = "'" <> T.replace "'" "\\'" (T.replace "\\" "\\\\" x) <> "'"

index :: Int -> [a] -> Maybe a
index i xs | i < 0 = Nothing
           | otherwise = case drop i xs of x:_ -> Just x; _ -> Nothing

integer :: Value -> Either Refusal Int
integer (Number n) = maybe (refuse Syntax "invalid-internal-index") Right (toBoundedInteger n)
integer _ = refuse Syntax "missing-internal-index"

generate :: Inventory -> Generated
generate original = Generated text report problems (null problems)
  where
    specialized = Specialize.prepare original
    inv = Specialize.inventory specialized
    concreteInstances = M.fromListWith (++) [(Specialize.origin i,[Specialize.identity i]) | i <- Specialize.instances specialized]
    requirements = S.toAscList (required inv)
    finiteDomains = M.fromList [(symbol,shape) | (symbol,d) <- M.toAscList (declarations inv)
      , S.member (symbol,"structure") (required inv), symbol /= builtin inv "bool"
      , Right shape <- [Finite.domain inv d]]
    finiteSymbols = S.fromList (concat [[Finite.domainSymbol shape] ++ Finite.constructors shape
      | shape <- M.elems finiteDomains])
    (algebraicShapes,algebraicErrors) = Algebraic.discover inv finiteDomains
    algebraicSymbols = Algebraic.symbols algebraicShapes
    functionResults = Algebraic.functions inv finiteDomains algebraicShapes
    relationResults = M.fromList [(symbol,Relation.relation inv finiteDomains def)
      | (symbol,"behavior") <- requirements, Just def <- [M.lookup symbol (declarations inv)]
      , get "kind" def == String "datatype"]
    emittedRelations = [rel | Right rel <- M.elems relationResults]
    relationSymbols = S.fromList (concat [[Relation.relationSymbol rel] ++ map Relation.ruleSymbol (Relation.rules rel)
      | rel <- emittedRelations])
    rawOutcomes = [((symbol,role),discharge symbol role) | (symbol,role) <- requirements]
    runtime = Specialize.runtimeClosure specialized
    runtimeVerified = not (S.null runtime)
      && runtime `S.isSubsetOf` S.fromList (map fst requirements)
      && all (\((s,role),result) -> not (S.member s runtime && role `elem` ["behavior","structure"])
          || either (const False) (const True) result) rawOutcomes
    retained = if not runtimeVerified then S.empty else S.fromList
      [(s,role) | ((s,role),Left _) <- rawOutcomes,role `elem` ["behavior","structure"]
        ,not (S.member s runtime),not (S.member s (Specialize.directRoots specialized))]
    outcomes = [(key,if S.member key retained then Right ("source.reduced-dependency",Nothing) else result)
      | (key,result) <- rawOutcomes]
    discharge symbol role = do
      def <- maybe (refuse Syntax "missing checked declaration") Right (M.lookup symbol (declarations inv))
      case role of
        "proof-source" -> Right ("source.proof",Nothing)
        "statement" -> Right ("source.statement",Nothing)
        "external-assumption" | get "kind" def == String "axiom" -> Right ("source.assumption",Nothing)
        _ | symbol `S.member` Specialize.levelSymbols original
          , not (null (Specialize.instances specialized))
          , not (S.member symbol (Specialize.directRoots specialized)) -> Right ("static.universe-level",Nothing)
        _ | Just reason <- M.lookup symbol (Specialize.failures specialized) -> Left reason
        _ | Right (Just _) <- Specialize.typeAlias original def -> Right ("static.type-alias",Nothing)
        _ | Just schema <- M.lookup symbol (Specialize.openRoots specialized) -> do
            _ <- discharge schema role
            Right ("native.open-parameters",Nothing)
        _ | Just uses <- M.lookup symbol concreteInstances
          , not (S.member symbol (Specialize.directRoots specialized)) -> do
            mapM_ (\s -> discharge s role) uses
            Right ("native.concrete-instantiations",Nothing)
        _ | symbol `elem` builtinValues -> Right ("native.boolean",Nothing)
        _ | symbol == builtin inv "nat", not (T.null symbol) -> Right ("native.natural-value",Nothing)
        _ | Just calc <- M.lookup symbol naturalConstructors -> Right ("native.natural-constructor",Just (AlgebraicCalculation calc))
        "structure" | S.member symbol finiteSymbols -> Right ("native.finite-domain",Nothing)
        "structure" | S.member symbol algebraicSymbols -> Right ("native.algebraic-value",Nothing)
        "structure" | S.member symbol relationSymbols -> Right ("native.finite-relation",Nothing)
        "structure" | Just reason <- M.lookup symbol algebraicErrors -> Left reason
        "behavior" | Just result <- M.lookup symbol relationResults -> do
          _ <- result
          Right ("native.finite-relation",Nothing)
        "behavior" | get "kind" def `elem` [String "function",String "primitive"] -> do
          case anchoredBoolean def of
            Right (arity,body) -> Right ("native.boolean-cases",Just (BooleanCalculation symbol arity body))
            Left booleanReason -> case Finite.function inv finiteDomains def of
              Right (shape,arity,body) -> Right ("native.finite-cases",Just (FiniteCalculation symbol shape arity body))
              Left finiteReason -> case M.findWithDefault (refuse Syntax "No checked first-order body") symbol functionResults of
                Right calc -> Right (if S.null (Algebraic.calls (Algebraic.body calc)) then "native.algebraic-cases"
                  else "native.first-order-calls",Just (AlgebraicCalculation calc))
                Left algebraicReason -> Left (alternatives [("native.boolean-cases",booleanReason),("native.finite-cases",finiteReason)]
                  ("native.algebraic-cases",algebraicReason))
        _ -> refuse Representation ("No direct target rule discharges this " <> role <> " requirement")
    anchoredBoolean def = do
      unless (length (array (get "sourceSyntax" def)) == 1)
        (refuse Syntax "The calculation has no uniquely anchored source definition")
      booleanFunction inv def
    builtinValues = filter (not . T.null) [builtin inv key | key <- ["bool","true","false"]]
    naturalConstructors = M.fromList [(Algebraic.calculationSymbol c,c) | c <- Algebraic.naturalCalculations inv]
    emitted = M.elems $ M.fromList ([(calculationSymbol calc,calc)
      | (_,Right (_,Just calc)) <- outcomes]
      ++ [(Algebraic.calculationSymbol c,AlgebraicCalculation c) | c <- Algebraic.constructorCalculations inv algebraicShapes])
    labels = M.fromListWith (+) [(display symbol,1 :: Int)
      | symbol <- S.toAscList (S.unions [finiteSymbols,relationSymbols,S.fromList (Algebraic.references algebraicShapes),S.fromList (map calculationSymbol emitted)])]
    sourceDisplay symbol = maybe symbol (string . get "displayName") (M.lookup symbol (declarations inv))
    helperNames = Algebraic.generatedNames sourceDisplay algebraicShapes
    display symbol = M.findWithDefault (sourceDisplay symbol) symbol helperNames
    targetLabel symbol = display symbol <> if M.findWithDefault 0 (display symbol) labels > 1
      then "#" <> T.take 16 (digest (TE.encodeUtf8 symbol)) else ""
    (text,trace) = D.renderBundle original inv rendered
    rendered = D.linesDoc (map D.text
      ["// " <> if null problems then "Complete translation of the declared required scope."
        else "INCOMPLETE: see diagnostics.json and correspondence.json."
      ,"package 'AgdaModel' {", "  private import ScalarValues::*;", "  private import ControlFunctions::*;"])
      <> mconcat [D.boundary (Finite.domainSymbol shape) "native.finite-domain" (Finite.enumText targetLabel shape) | shape <- M.elems finiteDomains]
      <> mconcat [let {symbol = Algebraic.shapeSymbol shape;
                      fragment = Algebraic.renderShapesIn targetLabel algebraicShapes (M.singleton symbol shape)}
                 in if maybe True ((/= Null) . get "nativeFamily") (M.lookup symbol (declarations inv))
                    then D.mark symbol "generated-family-shape" (D.generated "native.family-relation") (D.linesDoc (map D.text fragment))
                    else D.boundary symbol "native.algebraic-shape" fragment
                 | shape <- M.elems algebraicShapes]
      <> mconcat (map calculation emitted) <> mconcat (map (Relation.renderDoc targetLabel) emittedRelations)
      <> Presentation.renderCatalogue declarationCatalogue <> "}\n"
    calculation (AlgebraicCalculation c) = Algebraic.renderCalculationDoc inv algebraicShapes targetLabel c
    calculation definition = D.mark symbol "calculation" (D.derived "native.calculation" [D.root symbol "type"] Null []) $
      D.linesDoc ([D.text ("  calc def " <> quote (targetLabel symbol) <> " {")]
      ++ [D.text ("    in " <> quote ("input" <> T.pack (show i)) <> " : " <> typ <> ";") | i <- [0..arity-1]]
      ++ [D.text ("    return 'result' : " <> typ <> " = ") <> expressionDoc <> ";", "  }"])
      where
        (symbol,arity,typ,expressionDoc) = case definition of
          BooleanCalculation sym n body -> (sym,n,"Boolean",renderExprDoc sym body)
          FiniteCalculation sym shape n body -> (sym,n,quote (targetLabel (Finite.domainSymbol shape)),Finite.renderDoc targetLabel sym shape body)
    targetReference symbol = case [shape | shape <- M.elems finiteDomains, symbol `elem` Finite.constructors shape] of
      shape:_ -> "AgdaModel::" <> quote (targetLabel (Finite.domainSymbol shape)) <> "::" <> quote (targetLabel symbol)
      [] -> "AgdaModel::" <> quote (targetLabel symbol)
    obligations = [object ["symbol" .= symbol
      ,"kind" .= (if S.member (symbol,role) retained then "reduction-source" else role)
      ,"sourceKind" .= role, "source" .= sourceLink symbol
      ,"computational" .= S.member symbol runtime
      ,"retainedReason" .= (if S.member (symbol,role) retained
          then String "Checked preparation removed this dependency from every selected runtime root; its checked declaration and source remain in inventory.json."
          else Null)
      ,"instances" .= M.findWithDefault [] symbol concreteInstances
      ,"status" .= (case result of Left _ -> "textual"; Right _ -> "discharged" :: Text)
      ,"rule" .= (case result of Left _ -> Null; Right (r,_) -> String r)
      ,"reason" .= (case result of Left r -> String (message r); Right _ -> Null)
      ,"reasonCode" .= (case result of Left r -> String (code r); Right _ -> Null)
      ,"target" .= (case result of
          Right ("native.open-parameters",_) | Just schema <- M.lookup symbol (Specialize.openRoots specialized) ->
            String (if role == "structure" then structuralReference schema else targetReference schema)
          Right (_,Just _) -> String (targetReference symbol)
          Right (rule,_) | rule `elem` ["native.finite-domain","native.finite-relation","native.algebraic-value"] -> String (structuralReference symbol)
          _ -> Null)]
      | ((symbol,role),result) <- outcomes]
    structuralReference symbol = case [Algebraic.shapeSymbol sh | sh <- M.elems algebraicShapes
        ,Algebraic.isRecord sh,c <- Algebraic.variants sh,symbol `elem` map fst (Algebraic.payload c)] of
      owner:_ -> targetReference owner <> "::" <> quote (targetLabel symbol)
      [] -> targetReference symbol
    problems = [object ["code" .= code reason
      ,"severity" .= ("error" :: Text), "symbol" .= symbol, "kind" .= role
      ,"models" .= [modelId | (modelId,needs) <- M.toAscList (modelRequirements inv), S.member (symbol,role) needs]
      ,"source" .= sourceLink symbol, "message" .= message reason, "causes" .= causes reason]
      | ((symbol,role),Left reason) <- outcomes]
    sourceOrigin symbol = case M.lookup symbol (declarations inv) of
      Just d | String s <- get "higherOrderOrigin" d -> s
      Just d | String s <- get "specializationOrigin" d -> s
      _ -> symbol
    sourceLink symbol = object ["artifact" .= ("inventory.json" :: Text), "symbol" .= sourceOrigin symbol
      ,"module" .= maybe Null (get "sourceModule") (M.lookup symbol (declarations inv))
      ,"syntax" .= maybe Null (get "sourceSyntax") (M.lookup symbol (declarations inv))
      ,"checkedDefinition" .= sourceOrigin symbol]
    statuses = [object ["symbol" .= symbol, "id" .= get "id" def
      ,"required" .= S.member symbol requiredSymbols
      ,"representation" .= (if S.member symbol requiredSymbols && all (satisfied symbol) outcomes && any (native symbol) outcomes
          then "translated" else "textual" :: Text)
      ,"reason" .= (if S.member symbol requiredSymbols then Null else String "outside-required-scope")]
      | (symbol,def) <- M.toAscList (declarations inv)]
    requiredSymbols = S.map fst (required inv)
    native symbol ((other,_),Right (rule,_)) = symbol == other && "native." `T.isPrefixOf` rule
    native _ _ = False
    satisfied symbol ((other,_),result) = symbol /= other || case result of Right _ -> True; _ -> False
    linkModel model = let
      symbols = map string (array (get "symbols" (get "entry" (get "transition" model))))
      translated = S.unions [finiteSymbols,relationSymbols,S.fromList (map calculationSymbol emitted)]
      in case model of
        Object fields -> Object (KM.insert "transitionTargets" (toJSON
          [targetReference symbol | symbol <- symbols, S.member symbol translated]) fields)
        _ -> model
    modelLinks = case get "models" (document inv) of Object models -> Object (KM.map linkModel models); _ -> object []
    reductions value@(Object fields) = [e | let e = get "reductionEvidence" value,e /= Null]
      ++ concat [reductions v | (k,v) <- KM.toList fields,k `notElem` ["$occurrence","reductionEvidence"]]
    reductions (Array values) = concatMap reductions (foldr (:) [] values)
    reductions _ = []
    declarationCatalogue = if get "selectionProfile" (document original) == String "declarations"
      then Presentation.catalogue original obligations else []
    report = object ["sourceCorrespondence" .= trace,"schemaVersion" .= (1 :: Int), "obligations" .= obligations,"models" .= modelLinks
      ,"selectionProfile" .= get "selectionProfile" (document original)
      ,"declarationCatalogue" .= declarationCatalogue
      ,"specializations" .= [object ["symbol" .= Specialize.origin i,"instance" .= Specialize.identity i
        ,"arguments" .= map Specialize.typeValue (Specialize.arguments i)
        ,"targets" .= S.toAscList (S.fromList [target | o <- obligations,get "symbol" o == String (Specialize.identity i)
          ,String target <- [get "target" o]])]
        | i <- Specialize.instances specialized]
      ,"algebraicCarriers" .= Algebraic.carrierReport targetLabel algebraicShapes
      ,"indexContracts" .= [object ["symbol" .= Algebraic.calculationSymbol c
        ,"target" .= targetReference (Algebraic.calculationSymbol c)
        ,"constraints" .= Algebraic.calculationContracts targetLabel c]
        | AlgebraicCalculation c <- emitted,not (null (Algebraic.calculationContracts targetLabel c))]
      ,"calculationDependencies" .= [object ["symbol" .= Algebraic.calculationSymbol c
        ,"target" .= targetReference (Algebraic.calculationSymbol c)
        ,"callees" .= [object ["symbol" .= s,"target" .= targetReference s] | s <- S.toAscList (Algebraic.dependencies c)]]
        | AlgebraicCalculation c <- emitted,not (S.null (Algebraic.dependencies c))]
      ,"runtimeDependencyClosure" .= S.toAscList runtime
      ,"runtimeDependencyClosureVerified" .= runtimeVerified
      ,"retainedReductionSources" .= [object ["symbol" .= s,"sourceKind" .= role
          ,"untranslatedReason" .= message reason,"reasonCode" .= code reason]
        | ((s,role),Left reason) <- rawOutcomes,S.member (s,role) retained]
      ,"preparationEvidence" .= [object ["symbol" .= s
          ,"closureSpecialization" .= get "closureSpecialization" d
          ,"reductions" .= reductions compiled]
        | s <- S.toAscList runtime,Just d <- [M.lookup s (declarations inv)]
        ,Right compiled <- [field inv "compiled" d]
        ,get "closureSpecialization" d /= Null || not (null (reductions compiled))]
      ,"definitions" .= statuses, "complete" .= null problems
      ,"coverage" .= object ["inspectedDefinitions" .= M.size (declarations original)
        ,"specializedDefinitions" .= length (Specialize.instances specialized)
        ,"requiredDefinitions" .= S.size requiredSymbols, "requiredObligations" .= length outcomes
        ,"dischargedObligations" .= (length outcomes - length problems)
        ,"runtimeDefinitions" .= S.size runtime,"retainedReductionObligations" .= S.size retained]]

builtin :: Inventory -> Text -> Text
builtin inv key = string (get key (get "builtins" (document inv)))

booleanFunction :: Inventory -> Value -> Either Refusal (Int,Expr)
booleanFunction inv def = do
  ty <- field inv "type" def
  names <- telescope ty
  tree <- field inv "compiled" def
  body <- lower [Input i | i <- [0..length names-1]] tree
  pure (length names,body)
  where
    boolean ty = let t = get "term" ty in get "tag" t == String "definition"
      && get "symbol" t == String (builtin inv "bool") && get "eliminations" t == toJSON ([] :: [Value])
    telescope ty = let t = get "term" ty in
      if get "tag" t == String "pi" then do
        let dom = get "domain" t
        unless (boolean (get "type" dom)) (refuse Representation "The native Boolean rule requires Boolean inputs")
        rest <- telescope (get "body" (get "codomain" t))
        pure (() : rest)
      else if boolean ty then Right [] else refuse Representation "The native Boolean rule requires a Boolean result"
    lower env tree = fmap (located "native.boolean-case" tree (toJSON [renderExpr x | x <- env])) $ case string (get "tag" tree) of
      "done" -> do
        unless (length (array (get "binders" tree)) == length env) (refuse Syntax "Case leaf binder count does not match its environment")
        expression (reverse env) (get "body" tree)
      "case" -> do
        unless (get "copattern" tree == Bool False && get "eta" tree == Null
          && null (array (get "literals" tree)) && get "catchall" tree == Null
          && get "lazy" tree == Bool False && get "fallThrough" tree == Bool False)
          (refuse Semantics "This case tree needs a rule for additional match behavior")
        i <- integer (get "value" (get "argument" tree))
        selected <- maybe (refuse Syntax "Case split index is outside its environment") Right (index i env)
        let branches = array (get "constructors" tree)
            reduced = take i env ++ drop (i+1) env
            branch key = case filter ((== String (builtin inv key)) . get "symbol") branches of
              [b] | get "arity" (get "branch" b) == Number 0 -> lower reduced (get "tree" (get "branch" b))
              _ -> refuse Semantics "The native Boolean rule needs each nullary constructor exactly once"
        unless (length branches == 2) (refuse Semantics "The native Boolean rule requires exactly two constructor branches")
        Conditional (located "native.boolean-discriminant" tree (toJSON i) selected) <$> branch "true" <*> branch "false"
      _ -> refuse Syntax "This compiled body has no finite Boolean case-tree translation"
    expression env term = fmap (located "native.boolean-term" term (toJSON [renderExpr x | x <- env])) $ do
      unless (null (array (get "eliminations" term))) (refuse Syntax "Eliminations need a separate target rule")
      case string (get "tag" term) of
        "variable" -> do
          i <- integer (get "index" term)
          maybe (refuse Syntax "Leaf variable is outside its environment") Right (index i env)
        "constructor"
          | get "symbol" term == String (builtin inv "true") -> Right (Literal True)
          | get "symbol" term == String (builtin inv "false") -> Right (Literal False)
        _ -> refuse Syntax "Leaf expression needs a separate direct target rule"
