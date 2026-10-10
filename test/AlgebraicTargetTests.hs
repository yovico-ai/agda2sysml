{-# LANGUAGE OverloadedStrings #-}
module Main where

import Agda2SysML.Inventory
import qualified Agda2SysML.Mapping as Mapping
import qualified Agda2SysML.Diagnostic as D
import qualified Agda2SysML.Derivation as Trace
import qualified Agda2SysML.AlgebraicTarget as A
import qualified Agda2SysML.FiniteTarget as F
import qualified Agda2SysML.Target as T
import qualified Agda2SysML.Specialize as P
import qualified Agda2SysML.Reduction as Reduction
import qualified Agda2SysML.UnusedParameters as UnusedParameters
import Control.Monad (forM_, unless)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Either (isLeft)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.Environment (getEnv)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (callProcess)

-- Compiler-shaped fixtures belong in the implementation suite, not in Agda.
named :: Text -> Value
named s = object ["term" .= object ["tag" .= ("definition" :: Text),"symbol" .= s,"eliminations" .= ([] :: [Value])]]

info :: Value
info = object ["relevance" .= ("relevant" :: Text),"quantity" .= ("unrestricted" :: Text)]

signature :: [Value] -> Value -> Value
signature [] res = res
signature (x:xs) res = object ["term" .= object ["tag" .= ("pi" :: Text)
  ,"domain" .= object ["type" .= x,"info" .= info]
  ,"codomain" .= object ["body" .= signature xs res,"binds" .= True]]]

set :: Key -> Value -> Value -> Value
set k v (Object fields) = Object (KM.insert k v fields)
set _ _ v = v

declaration :: Text -> Text -> Value -> Value
declaration s kind ty = object ["name" .= s,"displayName" .= s,"kind" .= kind
  ,"type" .= ty,"abstract" .= False,"parameters" .= (0 :: Int)]

application :: Value -> Value
application v = object ["tag" .= ("apply" :: Text),"argument" .= object ["value" .= v,"info" .= info]]

constructor :: Text -> [Value] -> Value
constructor c args = object ["tag" .= ("constructor" :: Text),"symbol" .= c,"eliminations" .= map application args]

variable :: Int -> [Text] -> Value
variable i fields = object ["tag" .= ("variable" :: Text),"index" .= i
  ,"eliminations" .= [object ["tag" .= ("project" :: Text),"symbol" .= f] | f <- fields]]

done :: Int -> Value -> Value
done n term = object ["tag" .= ("done" :: Text),"binders" .= replicate n Null,"body" .= term]

split :: Int -> [(Text,Int,Value)] -> Value
split i branches = object ["tag" .= ("case" :: Text),"argument" .= object ["value" .= i]
  ,"copattern" .= False,"eta" .= Null,"literals" .= ([] :: [Value]),"catchall" .= Null
  ,"lazy" .= False,"fallThrough" .= False,"constructors" .=
    [object ["symbol" .= c,"branch" .= object ["arity" .= n,"tree" .= tree]] | (c,n,tree) <- branches]]

eta :: Int -> Value -> Value
eta i tree = set "eta" (object ["constructor" .= ("pair" :: Text),"fields" .= (["flag","tone"] :: [Text])
  ,"branch" .= object ["arity" .= (2 :: Int),"tree" .= tree]]) (set "lazy" (Bool True) (split i []))

operation :: Text -> [Text] -> Text -> Value -> Value
operation s ins out tree = set "compiled" tree $ set "sourceSyntax" (toJSON [object []]) $
  declaration s "function" (signature (map named ins) (named out))

-- An independent evaluator of the target expression algebra checks lowering
-- over all fixture values, including constructions the Pilot cannot execute.
data Val = B Bool | Z Integer | Seq [Val] | E Text Text | R Text (M.Map Text Val) | Fn Text | Closure [Text] A.Expression [Val] (M.Map Text Val) | N deriving (Eq,Show)
eval :: [Val] -> A.Expression -> Val
eval = evalWith M.empty

evalWith :: M.Map Text A.Calculation -> [Val] -> A.Expression -> Val
evalWith table env = evalIn table env M.empty

evalIn :: M.Map Text A.Calculation -> [Val] -> M.Map Text Val -> A.Expression -> Val
evalIn _ env _ (A.Input i) = env !! i
evalIn _ _ _ (A.Literal b) = B b
evalIn _ _ _ (A.NumberLiteral n) = Z n
evalIn table env locals (A.Numeric op x y) = case (evalIn table env locals x,evalIn table env locals y) of
  (Z a,Z b) -> case op of
    "+" -> Z (a+b)
    "*" -> Z (a*b)
    "monus" -> Z (max 0 (a-b))
    "<" -> B (a<b)
    "==" -> B (a==b)
    _ -> error "unknown numeric operation"
  _ -> error "non-natural numeric argument"
evalIn table env locals (A.Sequence xs) = Seq (concatMap flatten (map (evalIn table env locals) xs))
  where flatten (Seq vs) = vs
        flatten v = [v]
evalIn table env locals (A.SequenceHead _ xs) = evalIn table env locals (A.SequenceOp "head" xs)
evalIn table env locals (A.SequenceOp op xs) = case evalIn table env locals xs of
  Seq values -> case (op,values) of
    ("head",x:_) -> x
    ("tail",_:rest) -> Seq rest
    ("isEmpty",_) -> B (null values)
    ("size",_) -> Z (toInteger (length values))
    _ -> error "sequence operation outside admitted domain"
  _ -> error "non-sequence argument"
evalIn _ _ _ (A.Enumeration t c) = E t c
evalIn table env locals (A.Construct t fields) = R t (M.fromList [(f,evalIn table env locals x) | (f,x) <- fields])
evalIn table env locals (A.Project x f) = case evalIn table env locals x of
  R _ fields -> M.findWithDefault N f fields
  value -> error ("projection from " ++ show value)
evalIn table env locals (A.Equal x y) = B (evalIn table env locals x == evalIn table env locals y)
evalIn table env locals (A.Conditional p yes no) = case evalIn table env locals p of
  B b -> evalIn table env locals (if b then yes else no)
  _ -> error "non-Boolean guard"
evalIn _ _ _ A.Absent = N
evalIn table env locals (A.Call s args) = case M.lookup s table of
  Nothing -> error ("missing helper " ++ show s)
  Just calc -> evalWith table (map (evalIn table env locals) args) (A.body calc)
evalIn table env locals (A.Apply callback argument) = case evalIn table env locals callback of
  Fn symbol -> evalIn table env locals (A.Call symbol argument)
  Closure names body captures lexical -> evalIn table captures
    (M.union (M.fromList (zip names (map (evalIn table env locals) argument))) lexical) body
  _ -> error "native invocation needs a callable value"

evalIn _ env locals (A.Lambda args _ body) = Closure (map fst args) body env locals
evalIn _ _ locals (A.Iterator name _) = locals M.! name

call :: Text -> [Value] -> [Text] -> Value
call s args fields = object ["tag" .= ("definition" :: Text),"symbol" .= s
  ,"eliminations" .= (map application args ++ [object ["tag" .= ("project" :: Text),"symbol" .= f] | f <- fields])]

check :: Bool -> String -> IO ()
check ok message = unless ok (fail message)

level :: Integer -> Value
level n = object ["constant" .= n,"maximum" .= ([] :: [Value])]

universeAt :: Value -> Value
universeAt l = object ["term" .= object ["tag" .= ("sort" :: Text),"sort" .= object
  ["tag" .= ("universe" :: Text),"kind" .= ("UType" :: Text),"level" .= l]]]

main :: IO ()
main = do
  familyParameterChecks
  constructorScopeChecks
  reductionChecks
  naturalChecks
  constructorFibreChecks
  automaticSelectionChecks
  let universe = universeAt (level 0)
      tone = set "constructors" (toJSON (["red","blue"] :: [Text])) (declaration "Tone" "datatype" universe)
      pair = set "induction" (String "Nothing") $ set "constructor" (String "pair") $
        set "fields" (toJSON (["flag","tone"] :: [Text])) (declaration "Pair" "record" universe)
      choice = set "constructors" (toJSON (["first","second","none"] :: [Text])) (declaration "Choice" "datatype" universe)
      projection f typ = set "projection" (object ["proper" .= ("Pair" :: Text),"index" .= (1 :: Int)]) $
        declaration f "function" (signature [named "Pair"] (named typ))
      selected = operation "selected" ["Pair","Choice"] "Bool" $
        split 1 [("first",2,eta 1 (split 3
                   [("true",0,done 3 (variable 1 [])),("false",0,done 3 (constructor "false" []))]))
                ,("second",1,split 1 [("red",0,done 1 (variable 0 ["flag"]))
                                     ,("blue",0,done 1 (constructor "false" []))])
                ,("none",0,done 1 (variable 0 ["flag"]))]
      rebuild = operation "rebuild" ["Pair"] "Pair" (eta 0 (done 2 (constructor "pair" [variable 1 [],variable 0 []])))
      package = operation "packageValue" ["Pair"] "Choice" (done 1 (constructor "first" [variable 0 [],constructor "false" []]))
      defs = M.fromList [(string (get "name" d),d) | d <-
        [declaration "Bool" "datatype" universe, declaration "true" "constructor" (named "Bool")
        ,declaration "false" "constructor" (named "Bool"),tone,pair,choice
        ,declaration "red" "constructor" (named "Tone"),declaration "blue" "constructor" (named "Tone")
        ,declaration "pair" "constructor" (signature [named "Bool",named "Tone"] (named "Pair"))
        ,declaration "first" "constructor" (signature [named "Pair",named "Bool"] (named "Choice"))
        ,declaration "second" "constructor" (signature [named "Tone"] (named "Choice"))
        ,declaration "none" "constructor" (named "Choice"),projection "flag" "Bool",projection "tone" "Tone"
        ,selected,rebuild,package]]
      needs = S.fromList [(s,if s `elem` ["selected","rebuild","packageValue","flag","tone"] then "behavior" else "structure")
        | s <- M.keys defs]
      inv = Inventory (object ["builtins" .= object ["bool" .= ("Bool" :: Text),"true" .= ("true" :: Text),"false" .= ("false" :: Text)]])
        defs M.empty (M.singleton "algebraic" needs)
      finite = M.singleton "Tone" (F.Domain "Tone" ["red","blue"])
      (shapes,errors) = A.discover inv finite
      lower d = either (fail . show) pure (A.function inv finite shapes d)
      recordValue b c = R "Pair" (M.fromList [("flag",B b),("tone",E "Tone" c)])
      choiceValue c fields = R "Choice" (M.fromList (("constructor",E "Choice.constructor-tag" c):fields))
      badCarrier label change = let
        altered = inv {declarations = M.adjust change "Pair" defs}
        (accepted,_) = A.discover altered finite
        in check (not (M.member "Pair" accepted) && not (M.member "Choice" accepted)) label
  check (M.size shapes == 2 && M.null errors) (show errors)
  closureChecks inv
  diagnosticChecks inv finite shapes
  helperProvenanceChecks
  inputIndexProvenanceChecks
  resultIndexProvenanceChecks
  pick <- lower selected
  rebuildCalc <- lower rebuild
  packageCalc <- lower package
  forM_ [False,True] $ \b -> forM_ ["red","blue"] $ \c -> do
    let before = recordValue b c
    check (eval [before] (A.body rebuildCalc) == before) "record reconstruction changed field order/types"
    let packed = eval [before] (A.body packageCalc)
    check (packed == choiceValue "first" [("first.payload0",before),("first.payload1",B False),("second.payload0",N)])
      "constructor lost payload, changed order, or retained inactive data"
    forM_ [False,True] $ \flag -> forM_ [False,True] $ \gate -> do
      let cmd = choiceValue "first" [("first.payload0",recordValue flag c),("first.payload1",B gate)]
      check (eval [before,cmd] (A.body pick) == B (flag && gate)) "nested payload split changed argument binding"
    forM_ ["red","blue"] $ \color -> check
      (eval [before,choiceValue "second" [("second.payload0",E "Tone" color)]] (A.body pick) == B (b && color == "red"))
      "heterogeneous enum payload split changed behavior"
    check (eval [before,choiceValue "none" []] (A.body pick) == B b) "nullary branch lost remaining input"
  badCarrier "parameterized carrier admitted" (set "parameters" (Number 1))
  badCarrier "abstract carrier admitted" (set "abstract" (Bool True))
  badCarrier "coinductive carrier admitted" (set "induction" (String "Just CoInductive"))
  badCarrier "missing field admitted" (set "fields" (toJSON (["flag"] :: [Text])))
  badCarrier "duplicate field admitted" (set "fields" (toJSON (["flag","flag"] :: [Text])))
  let missing = operation "bad" ["Choice"] "Bool" (split 0 [("none",0,done 0 (constructor "false" []))])
      arity = operation "bad" ["Pair"] "Pair" (split 0 [("pair",1,done 1 (variable 0 []))])
      dependent = inv {declarations = M.adjust (set "type" (signature [object ["term" .= variable 0 []]] (named "Pair"))) "pair" defs}
      recursive = inv {declarations = M.adjust (set "type" (signature [named "Pair",named "Tone"] (named "Pair"))) "pair" defs}
  check (isLeft (A.function inv finite shapes missing)) "inexhaustive constructor matching admitted"
  check (isLeft (A.function inv finite shapes arity)) "payload arity mismatch admitted"
  check (not (M.member "Pair" (fst (A.discover dependent finite)))) "dependent field admitted without correspondence"
  check (not (M.member "Pair" (fst (A.discover recursive finite)))) "recursive field admitted without correspondence"
  let helper s ins out term = operation s ins out (done (length ins) term)
      helpers =
        [helper "idBool" ["Bool"] "Bool" (variable 0 [])
        ,helper "idTone" ["Tone"] "Tone" (variable 0 [])
        ,helper "idPair" ["Pair"] "Pair" (variable 0 [])
        ,helper "zeroArg" [] "Bool" (constructor "false" [])
        ,helper "callZero" ["Bool"] "Bool" (call "zeroArg" [] [])
        ,helper "throughRecord" ["Pair"] "Bool" (call "idPair" [variable 0 []] ["flag"])
        ,helper "nested" ["Pair"] "Bool" (call "idBool" [call "throughRecord" [variable 0 []] []] [])
        ,helper "callSelected" ["Choice","Pair"] "Bool" (call "selected" [variable 0 [],variable 1 []] [])
        ,helper "fromCalls" ["Pair"] "Pair" (constructor "pair"
          [call "idBool" [variable 0 ["flag"]] [],call "idTone" [variable 0 ["tone"]] []])
        ,helper "throughConstruction" ["Pair"] "Bool" (call "fromCalls" [variable 0 []] ["flag"])
        ,set "displayName" (String "idBool") (operation "idBool#other" ["Bool"] "Bool"
          (split 0 [("true",0,done 0 (constructor "false" [])),("false",0,done 0 (constructor "true" []))]))
        ,helper "clashCaller" ["Bool"] "Bool" (call "idBool#other" [variable 0 []] [])]
      extend additions inventory = inventory
        {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations inventory)
        ,modelRequirements = M.map (S.union (S.fromList [(string (get "name" d),"behavior") | d <- additions])) (modelRequirements inventory)}
      callInventory = extend helpers inv
      checked = A.functions callInventory finite shapes
      table = M.mapMaybe (either (const Nothing) Just) checked
      calculate s args = evalWith table args (A.body (table M.! s))
      rejected message additions names = do
        let altered = extend additions callInventory
            results = A.functions altered finite shapes
        check (all (maybe False isLeft . (`M.lookup` results)) names) message
        check (not (T.complete (T.generate altered))) (message ++ ": strict generation claimed completion")
  check (all (either (const False) (const True)) checked) (show checked)
  forM_ [False,True] $ \b -> forM_ ["red","blue"] $ \c -> do
    let p = recordValue b c
        command = choiceValue "none" []
    check (calculate "nested" [p] == B b) "nested call changed result"
    check (calculate "callSelected" [command,p] == B b) "heterogeneous call argument order changed"
    check (calculate "fromCalls" [p] == p) "calls in record fields changed payload"
    check (calculate "throughConstruction" [p] == B b) "call failed to bind a constructed result in the callee context"
    check (calculate "callZero" [B b] == B False) "zero-argument invocation lost"
    check (calculate "clashCaller" [B b] == B (not b)) "display spelling replaced canonical callee identity"
  rejected "self recursion admitted" [helper "loop" ["Bool"] "Bool" (call "loop" [variable 0 []] [])] ["loop"]
  rejected "mutual recursion or transitive caller admitted"
    [helper "a" ["Bool"] "Bool" (call "b" [variable 0 []] [])
    ,helper "b" ["Bool"] "Bool" (call "a" [variable 0 []] [])
    ,helper "caller" ["Bool"] "Bool" (call "a" [variable 0 []] [])] ["a","b","caller"]
  rejected "signature-only helper admitted"
    [helper "broken" ["Bool"] "Bool" (object ["tag" .= ("lambda" :: Text)])
    ,helper "caller" ["Bool"] "Bool" (call "broken" [variable 0 []] [])] ["broken","caller"]
  rejected "missing helper admitted" [helper "missing" ["Bool"] "Bool" (call "absent" [variable 0 []] [])] ["missing"]
  rejected "partial application admitted" [helper "partial" ["Bool"] "Bool" (call "idBool" [] [])] ["partial"]
  rejected "overapplication admitted" [helper "over" ["Bool"] "Bool" (call "idBool" [variable 0 [],variable 0 []] [])] ["over"]
  rejected "wrong argument carrier admitted" [helper "wrong" ["Pair"] "Bool" (call "idBool" [variable 0 []] [])] ["wrong"]
  parameterizedChecks inv
  universeChecks inv
  composedChecks inv
  indexedChecks inv
  computedChecks inv
  indexedLookupChecks inv
  unusedParameterChecks inv
  callbackModel <- callableFieldChecks inv
  dependentCallbackModel <- dependentCallableChecks inv
  schemaRecordModel <- schemaRecordChecks inv
  statementModel <- equalityStatementChecks inv
  contextualModel <- contextualMembershipChecks inv
  moduleAliasChecks inv
  let generated = T.generate callInventory
  check (T.complete generated) (show (T.diagnostics generated))
  root <- getEnv "AGDA2SYSML_TEST_VALIDATOR"
  java <- getEnv "AGDA2SYSML_TEST_JAVA"
  withSystemTempDirectory "algebraic-target" $ \directory -> do
    let file = directory </> "model.sysml"
        library = root </> "share/agda2sysml-validator/sysml"
        p = "new 'Pair'('flag'=true,'tone'='Tone'::'red')"
        cmd tag x y z = "new 'Choice'('constructor'='Choice.constructor-tag'::'" ++ tag
          ++ "','first.payload0'=" ++ x ++ ",'first.payload1'=" ++ y ++ ",'second.payload0'=" ++ z ++ ")"
        first = cmd "first" p "true" "null"
        second = cmd "second" "null" "null" "'Tone'::'blue'"
        none = cmd "none" "null" "null" "null"
    Text.writeFile file (T.modelText generated <> "\n" <> callbackModel <> "\n" <> dependentCallbackModel <> "\n" <> schemaRecordModel <> "\n" <> statementModel <> "\n" <> contextualModel)
    callProcess (root </> "bin/agda2sysml-validate") [file]
    callProcess java ["--class-path",library </> "jupyter-sysml-kernel-0.58.0-all.jar"
      ,"test/TargetEvaluation.java",library </> "sysml.library",file
      ,"'flag'(" ++ p ++ ")","true"
      ,"'tone'(" ++ p ++ ") == 'Tone'::'red'","true"
      ,"'selected'(" ++ p ++ "," ++ first ++ ")","true"
      ,"'selected'(" ++ p ++ "," ++ second ++ ")","false"
      ,"'selected'(" ++ p ++ "," ++ none ++ ")","true"
      ,"'Choice.payload-valid'(" ++ first ++ ")","true"
      ,"'Choice.payload-valid'(" ++ second ++ ")","true"
      ,"'Choice.payload-valid'(" ++ none ++ ")","true"
      ,"'Choice.payload-valid'(" ++ cmd "first" p "null" "null" ++ ")","false"
      ,"'Choice.payload-valid'(" ++ cmd "none" p "true" "null" ++ ")","false"
      ,"SequenceFunctions::size('SchemaRecordFixture'::'produceSchema'().'producedFamily'.items) == 4","true"]
    callProcess java ["--class-path",library </> "jupyter-sysml-kernel-0.58.0-all.jar"
      ,"test/TargetEvaluation.java",library </> "sysml.library",file
      ,"'nested'(" ++ p ++ ")","true"
      ,"'throughRecord'(" ++ p ++ ")","true"
      ,"'callSelected'(" ++ second ++ "," ++ p ++ ")","false"
      ,"'callSelected'(" ++ first ++ "," ++ p ++ ")","true"
      ,"'callZero'(true)","false"
      ,"'clashCaller'(true)","false"
      ,"'clashCaller'(false)","true"
      ,"'EqualityFixture'::'unrelatedIdentity.law'(true)","true"
      ,"'EqualityFixture'::'unrelatedIdentity.law'(false)","true"
      ,"'EqualityFixture'::'unrelatedSymmetry.law'(true, true, 'EqualityFixture'::'witness'(true))","true"
      ,"'EqualityFixture'::'unrelatedComparison.law'(true, false)","false"]
  putStrLn "algebraic carrier, binding, rejection, and native evaluation checks passed"

equalityStatementChecks :: Inventory -> IO Text
equalityStatementChecks base = do
  let equal a b = object ["term" .= call "Claim" [a,b] []]
      family = set "constructors" (toJSON (["witness"] :: [Text])) $
        declaration "Claim" "datatype" (signature [named "Bool",named "Bool"] (universeAt (level 0)))
      witness = set "family" (String "Claim") $ declaration "witness" "constructor"
        (signature [named "Bool"] (equal (variable 0 []) (variable 0 [])))
      law s ty = set "compiled" Null $ declaration s "function" ty
      reflexive = law "unrelatedIdentity" (signature [named "Bool"] (equal (variable 0 []) (variable 0 [])))
      comparison = law "unrelatedComparison" (signature [named "Bool",named "Bool"] (equal (variable 1 []) (variable 0 [])))
      helper = operation "retainedFunction" ["Bool"] "Bool" (done 1 (variable 0 []))
      helperLaw = law "unrelatedCall" (signature [named "Bool"]
        (equal (call "retainedFunction" [variable 0 []] []) (variable 0 [])))
      projected = variable 0 ["flag"]
      fieldLaw = law "unrelatedField" (signature [named "Pair"] (equal projected projected))
      symmetry = law "unrelatedSymmetry" (signature [named "Bool",named "Bool",equal (variable 1 []) (variable 0 [])]
        (equal (variable 1 []) (variable 2 [])))
      badBinding = law "badBinding" (signature [named "Bool"] (equal (variable 5 []) (variable 0 [])))
      broken = operation "unavailableOperation" ["Bool"] "Bool" Null
      badDependency = law "badDependency" (signature [named "Bool"]
        (equal (call "unavailableOperation" [variable 0 []] []) (variable 0 [])))
      defs = [family,witness,reflexive,comparison,helper,helperLaw,fieldLaw,symmetry,badBinding,broken,badDependency]
      laws = ["unrelatedIdentity","unrelatedComparison","unrelatedCall","unrelatedField","unrelatedSymmetry","badBinding","badDependency"]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- defs]) (declarations base)
        ,document = set "builtins" (set "equality" (String "Claim") (get "builtins" (document base))) (document base)
        ,modelRequirements = M.singleton "statements" (S.fromList [(s,r) | s <- laws,r <- ["statement","proof-source"]])}
      generated = T.generate inv
      rows = array (get "nativeStatements" (T.correspondence generated))
      translated s = any (\r -> get "symbol" r == String s && get "status" r == String "translated") rows
  check (T.complete generated) (show (T.diagnostics generated))
  check (all translated ["unrelatedIdentity","unrelatedComparison","unrelatedCall","unrelatedField","unrelatedSymmetry"] && not (any translated ["badBinding","badDependency"]))
    ("statement admission lost bindings or concealed a dependency: " ++ show rows)
  let originalRows = array (get "obligations" (T.correspondence generated))
  check (all (\s -> any (\r -> get "symbol" r == String s && get "sourceKind" r == String "proof-source"
      && get "rule" r == String "source.proof" && get "target" r == Null) originalRows) laws)
    "native statements replaced retained proof provenance"
  check (not (any (\r -> get "symbol" r == String "unavailableOperation" && get "sourceKind" r == String "behavior") originalRows))
    "failed optional statement expanded the required runtime scope"
  check (not (any (\r -> get "symbol" r == String "flag" && get "sourceKind" r == String "behavior") originalRows))
    "reading a structural field introduced a standalone calculation requirement"
  check ("in 'input2'" `Text.isInfixOf` T.modelText generated) "equality premise witness was erased"
  check ("constraint def 'unrelatedSymmetry.law'" `Text.isInfixOf` T.modelText generated) "statement not rendered as a native constraint"
  pure (Text.replace "package 'AgdaModel' {" "package 'EqualityFixture' {" (T.modelText generated))

-- A callback supplies membership context, never stored function identity.
contextualMembershipChecks :: Inventory -> IO Text
contextualMembershipChecks base = do
  let fn = A.Callable [A.Boolean] A.Boolean
      ticket = A.Shape "ContextTicket" True
        [A.Constructor "contextTicket" [("ticketIndex",A.Boolean),("ticketValue",A.Boolean)] [A.Input 0]] [A.Boolean]
      envelope = (A.Shape "ContextEnvelope" True
        [A.Constructor "contextEnvelope" [("virtualContext",fn),("prefix",A.Boolean)
          ,("member",A.Fibre "ContextTicket" [A.Apply (A.Input 0) [A.Input 1]])] [A.Input 0]] [fn])
        {A.contextIndices = [0]}
      shapes = M.fromList [(A.shapeSymbol sh,sh) | sh <- [ticket,envelope]]
      term x = object ["term" .= x]
      v i = variable i []
      apply f x = set "eliminations" (toJSON [application x]) f
      callable = term (object ["tag" .= ("native-callable" :: Text),"input" .= named "Bool"
        ,"result" .= named "Bool","binds" .= True])
      family name xs = term (call name xs [])
      envelopeAt i = family "ContextEnvelope" [v i]
      construct = set "type" (signature [callable,named "Bool",family "ContextTicket" [apply (v 1) (v 0)]] (envelopeAt 2))
        $ operation "buildContextEnvelope" [] "Bool" (done 3 (constructor "contextEnvelope" [v 2,v 1,v 0]))
      reconstruct = set "type" (signature [callable,envelopeAt 0] (envelopeAt 1))
        $ operation "rebuildContextEnvelope" [] "Bool" (split 1
          [("contextEnvelope",2,done 3 (constructor "contextEnvelope" [v 2,v 1,v 0]))])
      observe = set "type" (signature [callable,envelopeAt 0] (named "Bool"))
        $ operation "readContextEnvelope" [] "Bool" (done 2 (variable 0 ["member","ticketValue"]))
      ctor = set "patternCaptures" (Number 1) $ declaration "contextEnvelope" "constructor" (named "Bool")
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- [construct,reconstruct,observe,ctor]]) (declarations base)}
  cs <- traverse (either (fail . show) pure . A.function inv M.empty shapes) [construct,reconstruct,observe]
  let [build,rebuild,readValue] = cs
  forM_ [False,True] $ \prefix -> forM_ [False,True] $ \payload -> do
    let member = R "ContextTicket" (M.fromList [("ContextTicket.index0",B (not prefix)),("ticketIndex",B (not prefix)),("ticketValue",B payload)])
        value = R "ContextEnvelope" (M.fromList [("prefix",B prefix),("member",member)])
    check (eval [Fn "suppliedIndex",B prefix,member] (A.body build) == value)
      "context construction stored a callback or changed the domain payload"
    check (eval [Fn "suppliedIndex",value] (A.body rebuild) == value)
      "context reconstruction read a fictional callback field"
    check (eval [Fn "suppliedIndex",value] (A.body readValue) == B payload)
      "context projection lost the nested payload"
  let wrong = set "compiled" (done 3 (constructor "contextEnvelope" [v 2,constructor "false" [],v 0])) construct
  check (isLeft (A.function inv M.empty shapes wrong))
    "a constructor accepted a member indexed by a different preceding value"
  let rendered = Text.unlines (["package 'ContextualFixture' {"] ++ A.renderShapes id shapes
        ++ concatMap (A.renderCalculation inv shapes id) cs ++ ["}"])
  check (not ("virtualContext" `Text.isInfixOf` rendered)
    && not ("ContextEnvelope.index0" `Text.isInfixOf` rendered))
    "contextual membership emitted stored function identity"
  check ("'buildContextEnvelope'::'input0'(" `Text.isInfixOf` rendered
    && "'rebuildContextEnvelope'::'result'.'member'.'ContextTicket.index0'" `Text.isInfixOf` rendered)
    "contextual membership constraints were omitted at construction or return"
  pure rendered

parameterizedChecks :: Inventory -> IO ()
parameterizedChecks base = do
  let sort0 = object ["term" .= object ["tag" .= ("sort" :: Text),"sort" .= object
        ["tag" .= ("universe" :: Text),"kind" .= ("UType" :: Text),"level" .= object
          ["constant" .= (0 :: Int),"maximum" .= ([] :: [Value])]]]]
      piType binds a b = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= a,"info" .= info]
        ,"codomain" .= object ["binds" .= binds,"body" .= b]]]
      varType i = object ["term" .= variable i []]
      applied s xs = object ["term" .= call s (map (get "term") xs) []]
      boxTy t = applied "Box" [t]
      generic = piType True sort0
      box = set "parameters" (Number 1) $ set "induction" (String "Nothing")
        $ set "constructor" (String "box") $ set "fields" (toJSON (["contents"] :: [Text]))
        $ declaration "Box" "record" (generic sort0)
      ctor = set "parameters" (Number 1) $ set "family" (String "Box")
        $ declaration "box" "constructor" (generic (piType False (varType 0) (boxTy (varType 0))))
      contents = set "projection" (object ["proper" .= ("Box" :: Text),"index" .= (2 :: Int)])
        $ declaration "contents" "function" (generic (piType False (boxTy (varType 0)) (varType 0)))
      function s declaredType tree = set "compiled" tree $ set "sourceSyntax" (toJSON [object []]) $ declaration s "function" declaredType
      retain = set "projection" (object ["proper" .= Null,"index" .= (2 :: Int)])
        $ function "genericRetain" (generic (piType False (boxTy (varType 0)) (boxTy (varType 0)))) (done 1 (variable 0 []))
      wrap = function "genericWrap" (generic (piType False (varType 0) (boxTy (varType 0))))
        (done 2 (constructor "box" [variable 0 []]))
      pick = function "genericPick" (generic (piType False (named "Bool")
        (piType False (varType 0) (piType False (varType 0) (varType 0)))))
        (split 1 [("true",0,done 3 (variable 1 [])),("false",0,done 3 (variable 0 []))])
      through s carrierType = function s (piType False (boxTy carrierType) carrierType)
        (done 1 (call "genericRetain" [variable 0 []] ["contents"]))
      wrapCaller s carrierType = function s (piType False carrierType (boxTy carrierType))
        (done 1 (call "genericWrap" [get "term" carrierType,variable 0 []] []))
      pickCaller = function "pickBool" (piType False (named "Bool") (piType False (named "Bool") (named "Bool")))
        (done 2 (call "genericPick" [get "term" (named "Bool"),variable 1 [],variable 0 [],constructor "false" []] []))
      marker = set "parameters" (Number 1) $ set "constructors" (toJSON (["marker"] :: [Text]))
        $ declaration "Marker" "datatype" (generic sort0)
      markerCtor = set "parameters" (Number 1) $ set "family" (String "Marker")
        $ declaration "marker" "constructor" (generic (applied "Marker" [varType 0]))
      markerFunction s carrierType = function s (piType False (named "Bool") (applied "Marker" [carrierType]))
        (done 1 (constructor "marker" []))
      twoParameters = generic . generic
      eitherTy a b = applied "Either" [a,b]
      eitherDef = set "parameters" (Number 2) $ set "constructors" (toJSON (["left","right"] :: [Text]))
        $ declaration "Either" "datatype" (twoParameters sort0)
      eitherCtor s i = set "parameters" (Number 2) $ set "family" (String "Either")
        $ declaration s "constructor" (twoParameters (piType False (varType i) (eitherTy (varType 1) (varType 0))))
      firstOr = function "firstOr" (twoParameters (piType False (varType 1)
        (piType False (eitherTy (varType 1) (varType 0)) (varType 1))))
        (split 3 [("left",1,done 4 (variable 0 [])),("right",1,done 4 (variable 1 []))])
      useEither = function "useEither" (piType False (named "Bool")
        (piType False (eitherTy (named "Bool") (named "Tone")) (named "Bool")))
        (done 2 (call "firstOr" [get "term" (named "Bool"),get "term" (named "Tone"),variable 1 [],variable 0 []] []))
      additions = [box,ctor,contents,retain,wrap,pick,through "readBoolBox" (named "Bool")
        ,through "readToneBox" (named "Tone"),wrapCaller "wrapBool" (named "Bool")
        ,wrapCaller "wrapTone" (named "Tone"),through "readNested" (boxTy (named "Bool")),pickCaller
        ,marker,markerCtor,markerFunction "markBool" (named "Bool"),markerFunction "markTone" (named "Tone")
        ,eitherDef,eitherCtor "left" 1,eitherCtor "right" 0,firstOr,useEither]
      defs = M.insert "Bool" (set "constructors" (toJSON (["true","false"] :: [Text])) (declarations base M.! "Bool"))
        $ M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
      added = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      inv = base {declarations = defs,modelRequirements = M.map (`S.union` added) (modelRequirements base)}
      specialized = P.prepare inv
      expanded = P.inventory specialized
      finite = M.fromList [(s,dom) | (s,d) <- M.toList (declarations expanded),Right dom <- [F.domain expanded d]]
      shapes = fst (A.discover expanded finite)
      table = M.mapMaybe (either (const Nothing) Just) (A.functions expanded finite shapes)
      calculate s args = evalWith table args (A.body (table M.! s))
      ty s = P.Named s []
      key s args = P.typeKey (P.Named s args)
      boxValue t value = R (key "Box" [t]) (M.singleton (key "contents" [t]) value)
      generated = T.generate inv
      bad d message = do
        let altered = inv {declarations = M.insert (string (get "name" d)) d (declarations inv)}
        check (not (T.complete (T.generate altered))) message
  check (M.null (P.failures specialized)) (show (P.failures specialized))
  check (T.complete generated) (show (T.diagnostics generated))
  check (key "Marker" [ty "Bool"] /= key "Marker" [ty "Tone"]) "phantom arguments collapsed"
  check (length [i | i <- P.instances specialized,P.origin i == "Box"] == 3) "nested concrete carrier missing or duplicate"
  check (length [i | i <- P.instances specialized,P.origin i == "genericRetain"] == 3) "omitted type arguments not recovered"
  forM_ [False,True] $ \b -> do
    let boxed = boxValue (ty "Bool") (B b)
    check (calculate "readBoolBox" [boxed] == B b) "specialized projection-like call changed Boolean value"
    check (calculate "wrapBool" [B b] == boxed) "specialized construction changed Boolean value"
    check (calculate "readNested" [boxValue (P.Named "Box" [ty "Bool"]) boxed] == boxed) "nested instantiation changed payload"
    forM_ [False,True] $ \x -> check (calculate "pickBool" [B b,B x] == B (b && x)) "static binder removal changed case selection"
    let args = [ty "Bool",ty "Tone"]
        choiceValue selected payloadValue = R (key "Either" args) (M.fromList
          [("constructor",E (key "Either" args <> ".constructor-tag") (key selected args))
          ,(key "left" args <> ".payload0",if selected == "left" then payloadValue else N)
          ,(key "right" args <> ".payload0",if selected == "right" then payloadValue else N)])
    check (calculate "useEither" [B b,choiceValue "left" (B (not b))] == B (not b)) "distinct type parameter order changed left payload"
    check (calculate "useEither" [B b,choiceValue "right" (E "Tone" "red")] == B b) "distinct type parameter order changed right payload"
  forM_ ["red","blue"] $ \c -> do
    let value = E "Tone" c
    check (calculate "readToneBox" [boxValue (ty "Tone") value] == value) "specialized projection changed enumeration value"
    check (calculate "wrapTone" [value] == boxValue (ty "Tone") value) "specialized constructor merged distinct instantiations"
  bad (set "compiled" (done 2 (call "genericWrap" [variable 1 [],variable 0 []] [])) wrap) "recursive generic helper admitted"
  bad (set "type" (generic (piType False (boxTy (varType 0)) (boxTy (varType 0)))) ctor) "recursive generic carrier admitted"
  bad (set "compiled" (done 1 (call "genericWrap" [get "term" (named "Tone"),variable 0 []] [])) (wrapCaller "wrapBool" (named "Bool")))
    "inconsistent concrete call arguments admitted"
  bad (set "projection" (object ["proper" .= ("Tone" :: Text),"index" .= (2 :: Int)]) contents)
    "wrong generic projection owner admitted"
  let openRoot = inv {document = set "models" (object ["generic" .= object
        ["transition" .= object ["entry" .= object ["symbols" .= (["genericWrap"] :: [Text])]]]]) (document inv)}
  check (not (T.complete (T.generate openRoot))) "concrete uses discharged an open generic root"
  let openInvariant = inv {document = set "models" (object ["generic" .= object
        ["invariants" .= [object ["predicate" .= object ["symbols" .= (["genericWrap"] :: [Text])]]]]]) (document inv)}
  check (not (T.complete (T.generate openInvariant))) "concrete uses discharged an open generic invariant"
  let needs = required inv
      without names = S.filter (\(s,_) -> s `notElem` names) needs
      perModel = inv {modelRequirements = M.fromList
        [("boolean",without ["wrapTone","readToneBox","readNested","markTone"])
        ,("tone",without ["wrapBool","readBoolBox","readNested","markBool","pickBool","useEither"])]}
      models = modelRequirements (P.inventory (P.prepare perModel))
  check (S.member (key "genericWrap" [ty "Bool"],"behavior") (models M.! "boolean")
    && not (S.member (key "genericWrap" [ty "Tone"],"behavior") (models M.! "boolean")))
    "Boolean model acquired another model's helper instance"
  check (S.member (key "genericWrap" [ty "Tone"],"behavior") (models M.! "tone")
    && not (S.member (key "genericWrap" [ty "Bool"],"behavior") (models M.! "tone")))
    "enumeration model acquired another model's helper instance"
  let sourceLinks = array (get "obligations" (T.correspondence generated))
  check (all (\o -> M.member (string (get "checkedDefinition" (get "source" o))) (declarations inv)) sourceLinks)
    "specialization source link points outside checked inventory"

universeChecks :: Inventory -> IO ()
universeChecks base = do
  let zero = P.Level (P.LevelExpr 0 M.empty)
      two = P.Level (P.LevelExpr 2 M.empty)
      huge = 10 ^ (40 :: Int)
      levelTerm n = object ["tag" .= ("level" :: Text),"level" .= level n]
      variableLevel i = object ["constant" .= (0 :: Int),"maximum" .=
        [object ["offset" .= (0 :: Int),"term" .= variable i []]]]
      piType binds a b = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= a,"info" .= info]
        ,"codomain" .= object ["binds" .= binds,"body" .= b]]]
      varType i = object ["term" .= variable i []]
      function s ty tree = set "compiled" tree $ set "sourceSyntax" (toJSON [object []]) $ declaration s "function" ty
      generic = piType True (named "Level#builtin") . piType True (universeAt (variableLevel 0))
      ident = function "polyIdentity" (generic (piType False (varType 0) (varType 0))) (done 3 (variable 0 []))
      inferred = set "projection" (object ["proper" .= Null,"index" .= (3 :: Int)])
        $ function "inferredIdentity" (generic (piType False (varType 0) (varType 0))) (done 1 (variable 0 []))
      pick = function "polyPick" (generic (piType False (named "Bool")
        (piType False (varType 0) (piType False (varType 0) (varType 0)))))
        (split 2 [("true",0,done 4 (variable 1 [])),("false",0,done 4 (variable 0 []))])
      caller s typ l = function s (piType False (named typ) (named typ))
        (done 1 (call "polyIdentity" [l,get "term" (named typ),variable 0 []] []))
      inferredCaller = function "inferHigh" (piType False (named "High") (named "High"))
        (done 1 (call "inferredIdentity" [variable 0 []] []))
      pickCaller = function "pickLevel" (piType False (named "Bool") (piType False (named "Bool") (named "Bool")))
        (done 2 (call "polyPick" [levelTerm 0,get "term" (named "Bool"),variable 1 [],variable 0 [],constructor "false" []] []))
      phantomTy l = object ["term" .= call "Phantom" [l] []]
      phantom = set "parameters" (Number 1) $ set "constructors" (toJSON (["phantom"] :: [Text]))
        $ declaration "Phantom" "datatype" (piType True (named "Level#builtin") (universeAt (level 0)))
      phantomCtor = set "parameters" (Number 1) $ set "family" (String "Phantom")
        $ declaration "phantom" "constructor" (piType True (named "Level#builtin") (phantomTy (variable 0 [])))
      mark s l = function s (piType False (named "Bool") (phantomTy l)) (done 1 (constructor "phantom" []))
      high = set "constructors" (toJSON (["high"] :: [Text])) $ declaration "High" "datatype" (universeAt (level 2))
      highCtor = set "family" (String "High") $ declaration "high" "constructor" (named "High")
      suc t = call "suc#builtin" [t] []
      maxLevel a b = call "max#builtin" [a,b] []
      primitiveTwo = maxLevel (suc (levelTerm 0)) (suc (suc (call "zero#builtin" [] [])))
      additions = [ident,inferred,pick,caller "useBool" "Bool" (levelTerm 0),caller "useHigh" "High" primitiveTwo
        ,inferredCaller,pickCaller,phantom,phantomCtor,mark "markZero" (levelTerm 0),mark "markTwo" primitiveTwo
        ,mark "markTwoAgain" (levelTerm 2),mark "markHuge" (levelTerm huge),high,highCtor]
      defs = M.insert "Bool" (set "constructors" (toJSON (["true","false"] :: [Text])) (declarations base M.! "Bool"))
        $ M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
      builtins = set "level" (String "Level#builtin") $ set "levelZero" (String "zero#builtin")
        $ set "levelSuc" (String "suc#builtin") $ set "levelMax" (String "max#builtin") $ get "builtins" (document base)
      added = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      inv = base {document = set "builtins" builtins (document base),declarations = defs
        ,modelRequirements = M.map (`S.union` added) (modelRequirements base)}
      prepared = P.prepare inv
      expanded = P.inventory prepared
      finite = M.fromList [(s,d) | (s,v) <- M.toList (declarations expanded),Right d <- [F.domain expanded v]]
      shapes = fst (A.discover expanded finite)
      table = M.mapMaybe (either (const Nothing) Just) (A.functions expanded finite shapes)
      calculate s args = evalWith table args (A.body (table M.! s))
      bad d message = do
        let changed = inv {declarations = M.insert (string (get "name" d)) d (declarations inv)}
        check (not (T.complete (T.generate changed))) message
  check (M.null (P.failures prepared)) (show (P.failures prepared))
  check (T.complete (T.generate inv)) (show (T.diagnostics (T.generate inv)))
  check (length [i | i <- P.instances prepared,P.origin i == "Phantom"] == 3)
    "phantom levels merged or equivalent expressions duplicated"
  check (any (\i -> P.origin i == "Phantom" && P.arguments i == [P.Level (P.LevelExpr huge M.empty)]) (P.instances prepared))
    "universe level overflowed a machine integer"
  check (any (\i -> P.origin i == "inferredIdentity" && P.arguments i == [two,P.Named "High" []]) (P.instances prepared))
    "omitted level was not recovered from the checked type universe"
  forM_ [False,True] $ \b -> do
    check (calculate "useBool" [B b] == B b) "level/type binder removal changed runtime argument"
    forM_ [False,True] $ \x -> check (calculate "pickLevel" [B b,B x] == B (b && x)) "static levels changed case index"
  check (calculate "useHigh" [E "High" "high"] == E "High" "high") "nonzero universe changed native value"
  check (calculate "inferHigh" [E "High" "high"] == E "High" "high") "inferred level changed native value"
  check (P.readType inv [] primitiveTwo == Right two) "registered zero/successor/maximum not normalized"
  check (isLeft (P.readType inv [] (levelTerm (-1)))) "negative universe accepted"
  check (isLeft (P.readType inv [] (object ["tag" .= ("meta" :: Text)]))) "unresolved meta accepted"
  check (P.constrainLevel M.empty (P.LevelExpr 2 (M.singleton (P.BoundLevel 0) 0)) 2 == Right M.empty)
    "ambiguous maximum guessed a level"
  check (P.constrainLevel M.empty (P.LevelExpr 2 (M.singleton (P.BoundLevel 0) 2)) 2 == Right (M.singleton 0 zero))
    "uniquely determined zero level was not inferred"
  check (isLeft (P.constrainLevel M.empty (P.LevelExpr 3 M.empty) 2)) "inconsistent level constraint accepted"
  forM_ [0..4] $ \constant -> forM_ [0..4] $ \offset -> forM_ [0..4] $ \target -> do
    let solutions = [x | x <- [0..target],max constant (x+offset) == target]
        solved = P.constrainLevel M.empty (P.LevelExpr constant (M.singleton (P.BoundLevel 0) offset)) target
    case solutions of
      [] -> check (isLeft solved) "unsatisfiable maximum constraint accepted"
      [x] -> check (solved == Right (M.singleton 0 (P.Level (P.LevelExpr x M.empty)))) "unique level solution lost"
      _ -> check (solved == Right M.empty) "nonunique maximum constraint guessed a solution"
  check (isLeft (P.readType inv [] (object ["tag" .= ("level" :: Text),"level" .=
    object ["constant" .= (0 :: Int),"maximum" .= [object ["offset" .= (-1 :: Int),"term" .= levelTerm 0]]]])))
    "negative level offset accepted"
  check (isLeft (P.readType inv [] (maxLevel (levelTerm 0) (object ["tag" .= ("meta" :: Text)]))))
    "unresolved maximum accepted"
  bad (caller "useBool" "Bool" (levelTerm 2)) "wrong type universe accepted"
  bad (caller "useHigh" "High" (call "lsuc" [levelTerm 1] [])) "unregistered same-spelling primitive accepted"
  bad (caller "useBool" "Bool" (get "term" (named "Bool"))) "type accepted in level position"
  bad (set "compiled" (done 3 (variable 2 [])) ident) "static level emitted as runtime value"
  bad (caller "useBool" "Bool" (variable 0 [])) "runtime value accepted as static level"
  bad (set "type" (piType False (named "Level#builtin") (named "Bool")) (caller "useBool" "Bool" (levelTerm 0)))
    "runtime Level input accepted"
  let ambiguous = set "type" (piType True (named "Level#builtin") (piType True (universeAt
        (object ["constant" .= (2 :: Int),"maximum" .= [object ["offset" .= (0 :: Int),"term" .= variable 0 []]]]))
        (piType False (varType 0) (varType 0)))) inferred
  bad ambiguous "ambiguous omitted level accepted"
  -- The same checked operations must work with symbolic levels, without
  -- choosing a concrete level or merging caller and template level slots.
  let relay = function "openRelay" (generic (piType False (varType 0) (varType 0)))
        (done 3 (call "inferredIdentity" [variable 0 []] []))
      openInv = inv {document = set "selectionProfile" (String "declarations") $ set "library" (String "test") $
          set "modules" (toJSON [object ["source" .= object ["library" .= ("test" :: Text)]
            ,"definitions" .= [ident,inferred,pick,relay]]]) (document inv)
        ,declarations = M.insert "openRelay" relay (declarations inv)
        ,modelRequirements = M.singleton "open" (S.fromList [(s,"behavior") | s <- ["polyIdentity","inferredIdentity","polyPick","openRelay"]])}
      openPrepared = P.prepare openInv
      openGenerated = T.generate openInv
      rigid i = P.LevelExpr 0 (M.singleton (P.RigidLevel i) 0)
      openType = P.Open 1 (rigid 0)
      openTable = M.mapMaybe (either (const Nothing) Just) $ A.functions (P.inventory openPrepared) finite
        (fst (A.discover (P.inventory openPrepared) finite))
      openCalc s = openTable M.! (P.openRoots openPrepared M.! s)
  check (T.complete openGenerated) (show (T.diagnostics openGenerated))
  check (all (\s -> P.arguments s == [P.Level (rigid 0),openType])
      [s | s <- P.instances openPrepared,P.origin s `elem` ["polyIdentity","inferredIdentity","polyPick"]])
    "symbolic levels were concretized or changed scope"
  forM_ [False,True] $ \x -> do
    forM_ ["polyIdentity","inferredIdentity","openRelay"] $ \s ->
      check (evalWith openTable [B x] (A.body (openCalc s)) == B x) "open level changed identity/call behavior"
    forM_ [False,True] $ \y -> forM_ [False,True] $ \z ->
      check (eval [B x,B y,B z] (A.body (openCalc "polyPick")) == B (if x then y else z))
        "open level changed a runtime case position"
  check (P.substitute [two] (P.Level (rigid 0)) == Right (P.Level (rigid 0)))
    "callee substitution captured a caller's open level"
  check (P.typeKey (P.Level (rigid 0)) /= P.typeKey (P.Level (rigid 1)))
    "distinct symbolic levels shared a static identity"
  let maxOpen = maxLevel (variable 0 []) (suc (variable 0 []))
      shifted = P.LevelExpr 0 (M.singleton (P.RigidLevel 0) 1)
  check (P.readType inv [Just (P.Level (rigid 0))] maxOpen == Right (P.Level shifted))
    "symbolic successor/maximum did not canonicalize"
  check (P.readType inv [Just (P.Level (rigid 0))] (maxLevel (levelTerm 1) (suc (variable 0 [])))
      == Right (P.Level shifted)) "dominated level constant changed symbolic identity"
  let wrong = set "compiled" (done 3 (call "polyIdentity"
        [suc (variable 2 []),variable 1 [],variable 0 []] [])) ident
      invalid = openInv {declarations = M.insert "polyIdentity" wrong (declarations openInv)}
  check (not (T.complete (T.generate invalid))) "mismatched symbolic universe was accepted"

indexedChecks :: Inventory -> IO ()
indexedChecks base = do
  let piType binds a b = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= a,"info" .= info]
        ,"codomain" .= object ["binds" .= binds,"body" .= b]]]
      family s xs = object ["term" .= call s xs []]
      flagType = family "Evidence"
      true = constructor "true" []
      false = constructor "false" []
      generic = piType True (named "Bool")
      evidence = set "constructors" (toJSON (["off","on"] :: [Text]))
        $ declaration "Evidence" "datatype" (generic (universeAt (level 0)))
      ctor c t indexValue = set "family" (String "Evidence")
        $ declaration c "constructor" (piType False (named t) (flagType [indexValue]))
      function s ty tree = set "compiled" tree $ set "sourceSyntax" (toJSON [object []]) $ declaration s "function" ty
      readAny = function "readEvidence" (generic (piType False (flagType [variable 0 []]) (named "Bool")))
        (split 1 [("off",1,done 2 (variable 0 [])),("on",1,done 2 true)])
      rebuild = function "rebuildEvidence" (generic (piType False (flagType [variable 0 []]) (flagType [variable 0 []])))
        (split 1 [("off",1,done 2 (constructor "off" [variable 0 []])),("on",1,done 2 (constructor "on" [variable 0 []]))])
      retain = set "projection" (object ["proper" .= Null,"index" .= (2 :: Int)])
        $ function "retainEvidence" (generic (piType False (flagType [variable 0 []]) (flagType [variable 0 []]))) (done 1 (variable 0 []))
      caller = function "readOff" (piType False (flagType [false]) (named "Bool"))
        (done 1 (call "readEvidence" [false,call "retainEvidence" [variable 0 []] []] []))
      single = function "readSingle" (piType False (flagType [false]) (named "Bool"))
        (split 0 [("off",1,done 1 (variable 0 []))])
      flags = set "constructors" (toJSON (["flagValue"] :: [Text]))
        $ declaration "Flags" "datatype" (generic (universeAt (level 0)))
      flagsCtor = set "family" (String "Flags") $ declaration "flagValue" "constructor"
        (generic (family "Flags" [variable 0 []]))
      makeFlag = function "makeFlag" (generic (family "Flags" [variable 0 []]))
        (done 1 (constructor "flagValue" [variable 0 []]))
      flagRead = function "flagRead" (generic (piType False (family "Flags" [variable 0 []]) (named "Bool")))
        (split 1 [("flagValue",1,done 2 (variable 1 []))])
      rebuildFixed = function "rebuildFixed" (piType False (family "Flags" [true]) (family "Flags" [true]))
        (split 0 [("flagValue",1,done 1 (constructor "flagValue" [variable 0 []]))])
      bundleFields = ["switch","witness","selectedFlag","flagWitness"] :: [Text]
      bundle = set "constructor" (String "bundle") $ set "induction" (String "Nothing")
        $ set "fields" (toJSON bundleFields) $ declaration "Bundle" "record" (universeAt (level 0))
      bundleCtor = set "family" (String "Bundle") $ declaration "bundle" "constructor"
        (generic (piType True (flagType [variable 0 []]) (generic (piType False (family "Flags" [variable 0 []]) (named "Bundle")))))
      projection f typ = set "projection" (object ["proper" .= ("Bundle" :: Text),"index" .= (1 :: Int)])
        $ declaration f "function" (piType True (named "Bundle") typ)
      bundleProjections = [projection "switch" (named "Bool"),projection "witness" (flagType [variable 0 ["switch"]])
        ,projection "selectedFlag" (named "Bool"),projection "flagWitness" (family "Flags" [variable 0 ["selectedFlag"]])]
      bundleSelect = function "bundleSelect" (piType True (named "Bundle") (flagType [variable 0 ["switch"]]))
        (done 1 (variable 0 ["witness"]))
      bundleRead = operation "bundleRead" ["Bundle"] "Bool" (done 1
        (call "readEvidence" [variable 0 ["switch"],call "bundleSelect" [variable 0 []] []] []))
      bundleEta = set "eta" (object ["constructor" .= ("bundle" :: Text),"fields" .= bundleFields
        ,"branch" .= object ["arity" .= (4 :: Int),"tree" .= done 4 (constructor "bundle" (map (\i -> variable i []) [3,2,1,0]))]])
        (set "lazy" (Bool True) (split 0 []))
      bundleRebuild = operation "bundleRebuild" ["Bundle"] "Bundle" bundleEta
      bundleMake = function "bundleMake" (generic (piType True (flagType [variable 0 []]) (generic (named "Bundle"))))
        (done 3 (constructor "bundle" [variable 2 [],variable 1 [],variable 0 [],constructor "flagValue" [variable 0 []]]))
      bundleConstructedSelect = function "bundleConstructedSelect" (piType False (named "Bool") (flagType [false]))
        (done 1 (call "bundleSelect" [constructor "bundle" [false,constructor "off" [variable 0 []],true,constructor "flagValue" [true]]] []))
      envelope = set "constructor" (String "envelope") $ set "induction" (String "Nothing")
        $ set "fields" (toJSON (["inner"] :: [Text])) $ declaration "Envelope" "record" (universeAt (level 0))
      envelopeCtor = set "family" (String "Envelope") $ declaration "envelope" "constructor"
        (piType False (named "Bundle") (named "Envelope"))
      inner = set "projection" (object ["proper" .= ("Envelope" :: Text),"index" .= (1 :: Int)])
        $ declaration "inner" "function" (piType False (named "Envelope") (named "Bundle"))
      nested = function "nestedSelect" (piType True (named "Envelope") (flagType [variable 0 ["inner","switch"]]))
        (done 1 (variable 0 ["inner","witness"]))
      sumBundle = set "constructors" (toJSON (["packedBundle","quietBundle"] :: [Text]))
        $ declaration "SumBundle" "datatype" (universeAt (level 0))
      packedBundle = set "family" (String "SumBundle") $ declaration "packedBundle" "constructor"
        (generic (piType True (flagType [variable 0 []]) (generic
          (piType False (family "Flags" [variable 0 []]) (named "SumBundle")))))
      quietBundle = set "family" (String "SumBundle") $ declaration "quietBundle" "constructor"
        (piType False (named "Bool") (named "SumBundle"))
      sumTree packed quiet = split 0 [("packedBundle",4,packed),("quietBundle",1,quiet)]
      sumRebuild = operation "sumRebuild" ["SumBundle"] "SumBundle"
        (sumTree (done 4 (constructor "packedBundle" (map (\i -> variable i []) [3,2,1,0])))
          (done 1 (constructor "quietBundle" [variable 0 []])))
      sumRead = operation "sumRead" ["SumBundle"] "Bool"
        (sumTree (done 4 (call "readEvidence" [variable 3 [],variable 2 []] [])) (done 1 (variable 0 [])))
      sumNested = operation "sumNested" ["SumBundle"] "SumBundle"
        (sumTree (split 1 [("off",1,done 4 (constructor "packedBundle"
            [variable 3 [],constructor "off" [variable 2 []],variable 1 [],variable 0 []]))
          ,("on",1,done 4 (constructor "packedBundle"
            [variable 3 [],constructor "on" [variable 2 []],variable 1 [],variable 0 []]))])
          (done 1 (constructor "quietBundle" [variable 0 []])))
      sumPrefix = operation "sumPrefix" ["SumBundle"] "SumBundle"
        (sumTree (split 0 [("true",0,done 3 (constructor "packedBundle" [true,variable 2 [],variable 1 [],variable 0 []]))
          ,("false",0,done 3 (constructor "packedBundle" [false,variable 2 [],variable 1 [],variable 0 []]))])
          (done 1 (constructor "quietBundle" [variable 0 []])))
      sumMake = function "sumMake" (generic (piType True (flagType [variable 0 []]) (generic
          (piType False (family "Flags" [variable 0 []]) (named "SumBundle")))))
        (done 4 (constructor "packedBundle" (map (\i -> variable i []) [3,2,1,0])))
      additions = [sumBundle,packedBundle,quietBundle,sumRebuild,sumRead,sumNested,sumPrefix,sumMake
        ,evidence,ctor "off" "Bool" false,ctor "on" "Tone" true,readAny,rebuild,retain,caller,single
        ,flags,flagsCtor,makeFlag,flagRead,rebuildFixed,bundle,bundleCtor,bundleSelect,bundleRead,bundleRebuild,bundleMake,bundleConstructedSelect
        ,envelope,envelopeCtor,inner,nested] ++ bundleProjections
      defs = M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
      added = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      inv = base {declarations = defs,modelRequirements = M.map (`S.union` added) (modelRequirements base)}
      finite = M.fromList [(s,d) | (s,v) <- M.toList defs,Right d <- [F.domain inv v]]
      (shapes,_) = A.discover inv finite
      table = M.mapMaybe (either (const Nothing) Just) (A.functions inv finite shapes)
      calculate s args = evalWith table args (A.body (table M.! s))
      value c b = R "Evidence" (M.fromList
        [("constructor",E "Evidence.constructor-tag" c),("Evidence.index0",B (c == "on"))
        ,("off.payload0",if c == "off" then b else N),("on.payload0",if c == "on" then b else N)])
      flagged b = R "Flags" (M.fromList [("constructor",E "Flags.constructor-tag" "flagValue")
        ,("Flags.index0",B b),("flagValue.payload0",B b)])
      bad d message = do
        let changed = inv {declarations = M.insert (string (get "name" d)) d (declarations inv)}
        check (not (T.complete (T.generate changed))) message
      sumValue tag evidenceValue enabled = R "SumBundle" (M.fromList
        [("constructor",E "SumBundle.constructor-tag" "packedBundle"),("packedBundle.payload0",B tag)
        ,("packedBundle.payload1",evidenceValue),("packedBundle.payload2",B enabled)
        ,("packedBundle.payload3",flagged enabled),("quietBundle.payload0",N)])
      quietValue datum = R "SumBundle" (M.fromList
        ([("constructor",E "SumBundle.constructor-tag" "quietBundle"),("quietBundle.payload0",B datum)]
        ++ [("packedBundle.payload" <> Text.pack (show i),N) | i <- [0..3 :: Int]]))
      generated = T.generate inv
  check (T.complete generated) (show (T.diagnostics generated))
  check (A.indexTypes (shapes M.! "Evidence") == [A.Boolean]) "finite family lost its index domain"
  forM_ [False,True] $ \b -> do
    let off = value "off" (B b)
    check (calculate "readEvidence" [B False,off] == B b) "indexed dispatch lost Boolean payload"
    check (calculate "rebuildEvidence" [B False,off] == off) "dependent result reconstruction changed value/index"
    check (calculate "readOff" [off] == B b) "omitted runtime index was not recovered"
    check (calculate "readSingle" [off] == B b) "impossible constructor was required in a fixed fibre"
    check (calculate "makeFlag" [B b] == flagged b) "constructor's variable result index was erased"
    check (calculate "flagRead" [B b,flagged b] == B b) "branch refinement changed earlier runtime input"
  check (calculate "rebuildFixed" [flagged True] == flagged True)
    "fixed fibre did not refine its constructor payload"
  forM_ ["red","blue"] $ \c -> do
    let on = value "on" (E "Tone" c)
    check (calculate "rebuildEvidence" [B True,on] == on) "dependent enumeration payload changed"
    check (calculate "readEvidence" [B True,on] == B True) "indexed branch selection changed"
  forM_ ([(False,value "off" (B b),B b) | b <- [False,True]]
    ++ [(True,value "on" (E "Tone" c),B True) | c <- ["red","blue"]]) $ \(tag,evidenceValue,observed) ->
    forM_ [False,True] $ \enabled -> do
      let packetValue = R "Bundle" (M.fromList [("switch",B tag),("witness",evidenceValue)
            ,("selectedFlag",B enabled),("flagWitness",flagged enabled)])
      let sumV = sumValue tag evidenceValue enabled
      forM_ ["sumRebuild","sumNested","sumPrefix"] $ \name ->
        check (calculate name [sumV] == sumV) "dependent sum matching/reconstruction changed payload or index"
      check (calculate "sumRead" [sumV] == observed) "dependent constructor helper lost its earlier index"
      check (calculate "sumMake" [B tag,evidenceValue,B enabled,flagged enabled] == sumV)
        "ordered dependent sum construction changed fields"
      check (calculate "bundleSelect" [packetValue] == evidenceValue) "dependent field projection lost its member"
      check (calculate "bundleRead" [packetValue] == observed) "helper lost receiver-specific index"
      check (calculate "bundleRebuild" [packetValue] == packetValue) "eta-expanded dependent field types lost their prefix"
      check (calculate "bundleMake" [B tag,evidenceValue,B enabled] == packetValue) "ordered dependent construction changed fields"
      check (calculate "nestedSelect" [R "Envelope" (M.singleton "inner" packetValue)] == evidenceValue)
        "nested projection lost dependent field ownership"
  forM_ [False,True] $ \b -> check (calculate "bundleConstructedSelect" [B b] == value "off" (B b))
    "projection of known construction did not retain its index"
  forM_ [False,True] $ \datum -> do
    let quiet = quietValue datum
    forM_ ["sumRebuild","sumNested","sumPrefix"] $ \name ->
      check (calculate name [quiet] == quiet) "inactive dependent payload affected another sum variant"
    check (calculate "sumRead" [quiet] == B datum) "independent sum alternative changed"
  bad (set "compiled" (done 4 (constructor "packedBundle" [variable 1 [],variable 2 [],variable 3 [],variable 0 []])) sumMake)
    "dependent sum construction swapped equal-domain indices"
  bad (set "type" (generic (piType False (flagType [variable 1 []]) (named "SumBundle"))) packedBundle)
    "dependent sum admitted a forward reference"
  bad (set "compiled" (sumTree (split 1 [("off",1,done 4 (constructor "packedBundle"
        [true,constructor "off" [variable 2 []],variable 1 [],variable 0 []]))
      ,("on",1,done 4 (constructor "packedBundle"
        [true,constructor "on" [variable 2 []],variable 1 [],variable 0 []]))])
      (done 1 (constructor "quietBundle" [variable 0 []]))) sumNested)
    "nested payload match violated an earlier index"
  bad (set "compiled" (split 0 [("packedBundle",3,done 3 (constructor "quietBundle" [false]))
    ,("quietBundle",1,done 1 (constructor "quietBundle" [variable 0 []]))]) sumRebuild)
    "dependent constructor split lost a payload position"
  bad (set "compiled" (split 0 [("quietBundle",1,done 1 (variable 0 []))]) sumRead)
    "dependent constructor branch omitted"
  bad (projection "witness" (flagType [variable 0 ["selectedFlag"]])) "projection declaration swapped equal-domain prefix fields"
  bad (set "projection" (object ["proper" .= ("Pair" :: Text),"index" .= (1 :: Int)]) (projection "switch" (named "Bool")))
    "foreign projection owner justified a dependent index"
  bad (set "type" (piType True (named "Bundle") (flagType [call "notAProjection" [variable 0 []] []])) bundleSelect)
    "arbitrary computed field index accepted"
  bad (set "compiled" (done 3 (constructor "bundle" [variable 0 [],variable 1 [],variable 2 [],constructor "flagValue" [variable 2 []]])) bundleMake)
    "construction silently swapped independent index fields"
  bad (set "type" (generic (piType True (flagType [variable 1 []]) (generic (piType False (family "Flags" [variable 0 []]) (named "Bundle"))))) bundleCtor)
    "out-of-scope constructor prefix reference accepted"
  bad (set "compiled" (split 1 [("off",1,done 2 (variable 0 []))]) readAny) "missing possible indexed branch accepted"
  bad (set "compiled" (done 1 (call "readEvidence" [true,variable 0 []] [])) caller) "helper accepted wrong fibre index"
  bad (set "compiled" (split 1 [("off",1,done 2 (constructor "on" [constructor "red" []]))
    ,("on",1,done 2 (constructor "on" [variable 0 []]))]) rebuild) "dependent result changed index"
  bad (ctor "off" "Bool" (constructor "red" [])) "foreign enumeration constructor accepted as Boolean index"
  bad (ctor "off" "Bool" (call "unknownIndex" [] [])) "computed index silently erased"
  bad (set "type" (piType False (named "Pair") (universeAt (level 0))) evidence) "nonfinite index domain accepted"
  bad (set "type" (generic (piType False (flagType [variable 0 []]) (flagType [variable 1 []])) ) (ctor "off" "Bool" false))
    "recursive indexed payload accepted"
  bad (set "compiled" (set "fallThrough" (Bool True) (split 0 [("off",1,done 1 (variable 0 []))])) single)
    "unsupported indexed matching mode accepted"
  check ("'Evidence.index0'" `Text.isInfixOf` T.modelText generated
    && "index-contract-" `Text.isInfixOf` T.modelText generated) "native fibre constraints missing"
  let report = T.correspondence generated
      carriers = array (get "algebraicCarriers" report)
  check (any (\c -> get "symbol" c == String "Evidence" && length (array (get "indices" c)) == 1) carriers)
    "index correspondence absent"

-- Static parameter removal must preserve runtime dependencies, including
-- omitted indices on projection-like calls and receiver-dependent fields.
composedChecks :: Inventory -> IO ()
composedChecks base = do
  let sort0 = universeAt (level 0)
      piType binds a b = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= a,"info" .= info]
        ,"codomain" .= object ["binds" .= binds,"body" .= b]]]
      generic = piType True sort0
      varType i = object ["term" .= variable i []]
      applied s args = object ["term" .= call s args []]
      evidence a b = applied "GenericEvidence" [get "term" a,b]
      packet a = applied "GenericPacket" [get "term" a]
      evidenceDef = set "parameters" (Number 1) $ set "constructors" (toJSON (["goff","gon"] :: [Text]))
        $ declaration "GenericEvidence" "datatype" (generic (piType False (named "Bool") sort0))
      evidenceCtor c tag = set "parameters" (Number 1) $ set "family" (String "GenericEvidence")
        $ declaration c "constructor" (generic (piType False (varType 0) (evidence (varType 0) (constructor tag []))))
      packetDef = set "parameters" (Number 1) $ set "constructor" (String "gpacket")
        $ set "induction" (String "Nothing") $ set "fields" (toJSON (["genabled","gevidence"] :: [Text]))
        $ declaration "GenericPacket" "record" (generic sort0)
      packetCtor = set "parameters" (Number 1) $ set "family" (String "GenericPacket")
        $ declaration "gpacket" "constructor" (generic (piType True (named "Bool")
          (piType False (evidence (varType 1) (variable 0 [])) (packet (varType 1)))))
      projection f ty = set "projection" (object ["proper" .= ("GenericPacket" :: Text),"index" .= (2 :: Int)])
        $ declaration f "function" ty
      enabled = projection "genabled" (generic (piType False (packet (varType 0)) (named "Bool")))
      member = projection "gevidence" (generic (piType True (packet (varType 0))
        (evidence (varType 1) (variable 0 ["genabled"]))))
      function s ty tree = set "compiled" tree $ set "sourceSyntax" (toJSON [object []]) $ declaration s "function" ty
      retaining = set "projection" (object ["proper" .= Null,"index" .= (3 :: Int)])
        $ function "gretain" (generic (piType True (named "Bool")
          (piType False (evidence (varType 1) (variable 0 [])) (evidence (varType 1) (variable 0 [])))))
          (done 1 (variable 0 []))
      selecting = set "projection" (object ["proper" .= Null,"index" .= (2 :: Int)])
        $ function "gselect" (generic (piType True (packet (varType 0))
          (evidence (varType 1) (variable 0 ["genabled"])))) (done 1 (variable 0 ["gevidence"]))
      rebuilding = function "grebuild" (generic (piType False (packet (varType 0)) (packet (varType 0))))
        (split 1 [("gpacket",2,done 3 (constructor "gpacket" [variable 1 [],variable 0 []]))])
      copying = function "gcopy" (generic (piType False (packet (varType 0)) (packet (varType 0))))
        (done 2 (constructor "gpacket" [variable 0 ["genabled"],call "gretain" [variable 0 ["gevidence"]] []]))
      constructing = function "gmake" (generic (piType False (varType 0) (packet (varType 0))))
        (done 2 (constructor "gpacket" [constructor "true" [],constructor "gon" [variable 0 []]]))
      use s target a = function s (piType False (packet a) (packet a))
        (done 1 (call target [get "term" a,variable 0 []] []))
      makeUse s a = function s (piType False a (packet a))
        (done 1 (call "gmake" [get "term" a,variable 0 []] []))
      selectUse = function "selectBoolPacket" (piType True (packet (named "Bool"))
        (evidence (named "Bool") (variable 0 ["genabled"])))
        (done 1 (call "gselect" [variable 0 []] []))
      switch a = applied "GenericSwitch" [get "term" a]
      switchDef = set "parameters" (Number 1) $ set "constructors" (toJSON (["gyes","gno"] :: [Text]))
        $ declaration "GenericSwitch" "datatype" (generic sort0)
      switchCtor c = set "parameters" (Number 1) $ set "family" (String "GenericSwitch")
        $ declaration c "constructor" (generic (switch (varType 0)))
      selected a tag = applied "Selected" [get "term" a,tag]
      selectedDef = set "parameters" (Number 1) $ set "constructors" (toJSON (["gselected"] :: [Text]))
        $ declaration "Selected" "datatype" (generic (piType False (switch (varType 0)) sort0))
      selectedCtor = set "parameters" (Number 1) $ set "family" (String "Selected")
        $ declaration "gselected" "constructor" (generic (piType True (switch (varType 0))
          (piType False (varType 1) (selected (varType 1) (variable 0 [])))))
      selectMake = function "makeSelected" (generic (piType False (varType 0) (selected (varType 0) (constructor "gyes" []))))
        (done 2 (constructor "gselected" [constructor "gyes" [],variable 0 []]))
      selectCaller = function "makeSelectedBool" (piType False (named "Bool") (selected (named "Bool") (constructor "gyes" [])))
        (done 1 (call "makeSelected" [get "term" (named "Bool"),variable 0 []] []))
      genEnvelope a tag = applied "PayloadEnvelope" [get "term" a,tag]
      genEnvelopeDef = set "parameters" (Number 1) $ set "constructors" (toJSON (["dependentMessage","plainMessage"] :: [Text]))
        $ declaration "PayloadEnvelope" "datatype" (generic (piType False (named "Bool") sort0))
      genMessage = set "parameters" (Number 1) $ set "family" (String "PayloadEnvelope")
        $ declaration "dependentMessage" "constructor" (generic (piType True (named "Bool")
          (piType False (evidence (varType 1) (variable 0 [])) (genEnvelope (varType 1) (variable 0 [])))))
      genPlain = set "parameters" (Number 1) $ set "family" (String "PayloadEnvelope")
        $ declaration "plainMessage" "constructor" (generic (piType False (varType 0)
          (genEnvelope (varType 0) (constructor "false" []))))
      genCopy = function "copyPayloadEnvelope" (generic (piType True (named "Bool")
        (piType False (genEnvelope (varType 1) (variable 0 [])) (genEnvelope (varType 1) (variable 0 [])))))
        (split 2 [("dependentMessage",2,done 4 (constructor "dependentMessage" [variable 1 [],variable 0 []]))
          ,("plainMessage",1,done 3 (constructor "plainMessage" [variable 0 []]))])
      copyEnvelope s typ tag = function s (piType False (genEnvelope typ (constructor tag [])) (genEnvelope typ (constructor tag [])))
        (done 1 (call "copyPayloadEnvelope" [get "term" typ,constructor tag [],variable 0 []] []))
      additions = [genEnvelopeDef,genMessage,genPlain,genCopy,copyEnvelope "copyFalseEnvelope" (named "Bool") "false"
        ,copyEnvelope "copyTrueEnvelope" (named "Tone") "true"
        ,switchDef,switchCtor "gyes",switchCtor "gno",selectedDef,selectedCtor,selectMake,selectCaller
        ,evidenceDef,evidenceCtor "goff" "false",evidenceCtor "gon" "true",packetDef,packetCtor
        ,enabled,member,retaining,selecting,rebuilding,copying,constructing
        ,use "copyBoolPacket" "gcopy" (named "Bool"),use "copyTonePacket" "gcopy" (named "Tone")
        ,use "rebuildBoolPacket" "grebuild" (named "Bool")
        ,makeUse "makeBoolPacket" (named "Bool"),makeUse "makeTonePacket" (named "Tone"),selectUse]
      defs = M.insert "Bool" (set "constructors" (toJSON (["true","false"] :: [Text])) (declarations base M.! "Bool"))
        $ M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
      added = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      inv = base {declarations = defs,modelRequirements = M.map (`S.union` added) (modelRequirements base)}
      prepared = P.prepare inv
      expanded = P.inventory prepared
      finite = M.fromList [(s,d) | (s,v) <- M.toList (declarations expanded),Right d <- [F.domain expanded v]]
      shapes = fst (A.discover expanded finite)
      table = M.mapMaybe (either (const Nothing) Just) (A.functions expanded finite shapes)
      calculate s args = evalWith table args (A.body (table M.! s))
      key s typ = P.typeKey (P.Named s [P.Named typ []])
      evidenceValue typ tag value = R (key "GenericEvidence" typ) (M.fromList
        [("constructor",E (key "GenericEvidence" typ <> ".constructor-tag") (key (if tag then "gon" else "goff") typ))
        ,(key "GenericEvidence" typ <> ".index0",B tag)
        ,(key "goff" typ <> ".payload0",if tag then N else value)
        ,(key "gon" typ <> ".payload0",if tag then value else N)])
      packetValue typ tag value = R (key "GenericPacket" typ) (M.fromList
        [(key "genabled" typ,B tag),(key "gevidence" typ,evidenceValue typ tag value)])
      bad d message = do
        let altered = inv {declarations = M.insert (string (get "name" d)) d (declarations inv)}
        check (not (T.complete (T.generate altered))) message
  check (M.null (P.failures prepared)) (show (P.failures prepared))
  check (T.complete (T.generate inv)) (show (T.diagnostics (T.generate inv)))
  check (length [i | i <- P.instances prepared,P.origin i == "GenericEvidence"] == 2)
    "runtime indices split static family identities"
  forM_ [False,True] $ \tag -> do
    forM_ [False,True] $ \value -> do
      let packetV = packetValue "Bool" tag (B value)
      check (calculate "copyBoolPacket" [packetV] == packetV) "omitted static/runtime indices changed copying"
      check (calculate "rebuildBoolPacket" [packetV] == packetV) "specialized dependent eta expansion changed fields"
      check (calculate "selectBoolPacket" [packetV] == evidenceValue "Bool" tag (B value)) "specialized receiver index was lost"
      check (calculate "makeBoolPacket" [B value] == packetValue "Bool" True (B value)) "specialized construction changed index/payload"
    forM_ ["red","blue"] $ \color -> do
      let value = E "Tone" color; packetV = packetValue "Tone" tag value
      check (calculate "copyTonePacket" [packetV] == packetV) "distinct payload specialization changed copying"
      check (calculate "makeTonePacket" [value] == packetValue "Tone" True value) "enumeration payload became Boolean"
  forM_ [False,True] $ \b -> do
    let tag = E (key "GenericSwitch" "Bool") (key "gyes" "Bool")
        expected = R (key "Selected" "Bool") (M.fromList
          [("constructor",E (key "Selected" "Bool" <> ".constructor-tag") (key "gselected" "Bool"))
          ,(key "Selected" "Bool" <> ".index0",tag)
          ,(key "gselected" "Bool" <> ".payload0",tag),(key "gselected" "Bool" <> ".payload1",B b)])
    check (calculate "makeSelectedBool" [B b] == expected) "specialized enumeration index lost its static domain"
  bad (set "compiled" (done 2 (constructor "gselected" [constructor "gno" [],variable 0 []])) selectMake)
    "specialized enumeration constructor violated a fixed result index"
  let envelopeValue typ tag value = R (key "PayloadEnvelope" typ) (M.fromList
        [("constructor",E (key "PayloadEnvelope" typ <> ".constructor-tag") (key "dependentMessage" typ))
        ,(key "PayloadEnvelope" typ <> ".index0",B tag)
        ,(key "dependentMessage" typ <> ".payload0",B tag)
        ,(key "dependentMessage" typ <> ".payload1",evidenceValue typ tag value)
        ,(key "plainMessage" typ <> ".payload0",N)])
  forM_ [False,True] $ \b -> do
    let expected = envelopeValue "Bool" False (B b)
    check (calculate "copyFalseEnvelope" [expected] == expected)
      "specialized indexed sum reconstruction lost dependent member"
  forM_ ["red","blue"] $ \color -> do
    let expected = envelopeValue "Tone" True (E "Tone" color)
    check (calculate "copyTrueEnvelope" [expected] == expected)
      "fixed outer fibre changed specialized dependent payload"
  bad (set "compiled" (done 2 (constructor "gpacket" [constructor "false" [],constructor "gon" [variable 0 []]])) constructing)
    "static specialization erased an inconsistent runtime index"
  bad (projection "gevidence" (generic (piType False (packet (varType 0)) (evidence (varType 0) (constructor "false" [])))))
    "static specialization erased a malformed dependent projection"
  bad (set "projection" (object ["proper" .= ("Tone" :: Text),"index" .= (2 :: Int)]) member)
    "static specialization changed projection ownership"
  bad (set "compiled" (done 1 (call "gcopy" [get "term" (named "Tone"),variable 0 []] []))
    (use "copyBoolPacket" "gcopy" (named "Bool"))) "different static payload types unified"

-- Compiler-provided module equations determine carrier identity; names and
-- structurally similar constructor results do not establish an alias.
moduleAliasChecks :: Inventory -> IO ()
moduleAliasChecks base = do
  let alias = set "moduleInstanceCopy" (Bool True) $ set "moduleAlias"
        (object ["telescope" .= ([] :: [Value]),"patterns" .= ([] :: [Value]),"body" .= call "Pair" [] []]) $
        declaration "CopiedPair" "record" (universeAt (level 0))
      inv = base {declarations = M.insert "CopiedPair" alias (declarations base)}
      readAlias i = P.readType i [] (call "CopiedPair" [] [])
  check (readAlias inv == Right (P.Named "Pair" [])) "checked module carrier alias was not followed"
  forM_ [set "moduleAlias" Null,set "abstract" (Bool True)
        ,set "moduleAlias" (object ["telescope" .= [Null],"patterns" .= [object ["value" .= constructor "true" []]]
            ,"body" .= call "Pair" [] []])] $ \change ->
    check (isLeft (readAlias inv {declarations = M.adjust change "CopiedPair" (declarations inv)}))
      "absent, opaque or matching carrier equation was assumed to be an alias"
  let safe = set "opaque" (Bool False) . set "terminates" (Bool True) . set "sourceModule" (String "Copied")
      original = safe $ operation "sourceIdentity" ["Bool"] "Bool" (done 1 (variable 0 []))
      copied = safe $ set "moduleInstanceCopy" (Bool True) $ set "sourceSyntax" (toJSON ([] :: [Value])) $
        operation "copiedIdentity" ["Bool"] "Bool" (done 1 (call "sourceIdentity" [variable 0 []] []))
      functions = inv {declarations = M.insert "sourceIdentity" original $ M.insert "copiedIdentity" copied (declarations inv)
        ,document = set "checking" (toJSON [object ["module" .= ("Copied" :: Text),"safe" .= True,"terminationCheck" .= True]]) (document inv)
        ,modelRequirements = M.singleton "copy" (S.fromList [("sourceIdentity","behavior"),("copiedIdentity","behavior")])}
      calculations i = A.functions i M.empty M.empty
  check (either (const False) (const True) (calculations functions M.! "copiedIdentity"))
    "checked module function alias requires nonexistent standalone syntax"
  forM_ [set "moduleInstanceCopy" (Bool False),set "terminates" (Bool False)
        ,set "compiled" (done 1 (call "missing" [variable 0 []] []))] $ \change ->
    check (isLeft (calculations functions {declarations = M.adjust change "copiedIdentity" (declarations functions)} M.! "copiedIdentity"))
      "unanchored or unsupported module alias was accepted"

-- Unused higher-order module parameters are static only after dependency checks.
unusedParameterChecks :: Inventory -> IO ()
unusedParameterChecks base = do
  let callback = signature [named "Bool"] (named "Bool")
      ty s args = object ["term" .= call s args []]
      v i = variable i []
      parameterized = set "moduleParameters" (Number 1)
      safe = parameterized . set "opaque" (Bool False) . set "terminates" (Bool True)
        . set "sourceModule" (String "UnusedChecked")
      carrier = parameterized $ set "parameters" (Number 1) $ set "constructors" (toJSON (["wrapUnused"] :: [Text])) $
        declaration "PhantomCallback" "datatype" (signature [callback] (universeAt (level 0)))
      ctor = parameterized $ set "parameters" (Number 1) $ set "family" (String "PhantomCallback") $
        declaration "wrapUnused" "constructor" (signature [callback,named "Bool"] (ty "PhantomCallback" [v 1]))
      passthrough = safe $ set "type" (signature [callback,ty "PhantomCallback" [v 0]] (ty "PhantomCallback" [v 1])) $
        operation "passUnused" [] "Bool" (done 2 (v 0))
      forwarded = safe $ set "type" (signature [callback,ty "PhantomCallback" [v 0]] (ty "PhantomCallback" [v 1])) $
        operation "forwardUnused" [] "Bool" (done 2 (call "passUnused" [v 1,v 0] []))
      used = safe $ set "type" (signature [callback,named "Bool"] (named "Bool")) $
        operation "usedCallback" [] "Bool" (done 2 (set "eliminations" (toJSON [application (v 0)]) (v 1)))
      transitivelyUsed = safe $ set "type" (signature [callback,named "Bool"] (named "Bool")) $
        operation "forwardUsed" [] "Bool" (done 2 (call "usedCallback" [v 1,v 0] []))
      declarations' = [carrier,ctor,passthrough,forwarded,used,transitivelyUsed]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- declarations']) (declarations base)
        ,document = set "selectionProfile" (String "declarations") $ set "library" (String "test") $
          set "modules" (toJSON [object ["source" .= object ["library" .= ("test" :: Text)],"definitions" .= declarations']]) $
          set "checking" (toJSON [object ["module" .= ("UnusedChecked" :: Text),"safe" .= True,"terminationCheck" .= True]]) (document base)
        ,modelRequirements = M.singleton "unused" (S.fromList [(string (get "name" d),
            if get "kind" d == String "function" then "behavior" else "structure") | d <- declarations'])}
      omitted inventory s = get "unusedModuleParameters" (declarations (UnusedParameters.annotate inventory) M.! s)
      prepared = P.prepare inv
      expanded = P.inventory prepared
      shapes = fst (A.discover expanded M.empty)
      calculations = A.functions expanded M.empty shapes
  forM_ ["PhantomCallback","wrapUnused","passUnused","forwardUnused"] $ \s ->
    check (omitted inv s == toJSON ([0] :: [Int])) ("unused forwarding not established: " ++ show s)
  forM_ ["usedCallback","forwardUsed"] $ \s -> do
    check (omitted inv s == toJSON ([] :: [Int])) "live callback was classified unused"
    check (M.notMember s (P.failures prepared)) (show (P.failures prepared))
    calc <- either (fail . show) pure (calculations M.! s)
    check (A.inputs calc == [A.Callable [A.Boolean] A.Boolean,A.Boolean]) "callback signature lost its domain or result"
    check ("in calc 'input0'" `Text.isInfixOf` Text.unlines (A.renderCalculation expanded shapes id calc))
      "callback was not emitted as a native calculation input"
  callbackCalc <- either (fail . show) pure (calculations M.! "usedCallback")
  check (A.body callbackCalc == A.Apply (A.Input 0) [A.Input 1]) "callback application was not retained"
  let identity = A.Calculation "identity" [A.Boolean] A.Boolean (A.Input 0) []
      invert = A.Calculation "invert" [A.Boolean] A.Boolean
        (A.Conditional (A.Input 0) (A.Literal False) (A.Literal True)) []
      table = M.union (M.fromList [("identity",identity),("invert",invert)])
        (M.mapMaybe (either (const Nothing) Just) calculations)
  forM_ ["usedCallback","forwardUsed"] $ \symbol -> forM_ [False,True] $ \value ->
    forM_ [("identity",value),("invert",not value)] $ \(fn,expected) ->
      check (evalWith table [Fn fn,B value] (A.body (table M.! symbol)) == B expected)
        "native callback invocation/forwarding changed the supplied function"
  let preparedBody definition =
        let input = inv {declarations = M.insert "usedCallback" definition (declarations inv)}
            transformed = P.prepare input
            target = P.inventory transformed
        in (transformed,A.functions target M.empty (fst (A.discover target M.empty)))
      wrongArgument = set "compiled" (done 2 (set "eliminations"
        (toJSON [application (constructor "red" [])]) (v 1))) used
      (_,wrongCalculations) = preparedBody wrongArgument
  check (maybe True isLeft (M.lookup "usedCallback" wrongCalculations)) "ill-typed callback application admitted"
  check (isLeft (P.readType inv [] (get "term" (signature [callback] (named "Bool")))))
    "higher-order callback domain admitted by unary rule"
  check (P.readType inv [] (get "term" (signature [named "Bool",named "Bool"] (named "Bool"))) == Right (P.Callable [P.Named "Bool" [],P.Named "Bool" []] (P.Named "Bool" [])))
    "multiargument callback telescope was not retained"
  let dependent = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= info,"type" .= named "Bool"]
        ,"codomain" .= object ["binds" .= True,"body" .= object ["term" .= v 0]]]]
  check (isLeft (P.readType inv [] (get "term" dependent))) "dependent callback result admitted"
  forM_ ["passUnused","forwardUnused"] $ \s -> do
    key <- maybe (fail (show (s,P.failures prepared))) pure (M.lookup s (P.openRoots prepared))
    calc <- either (fail . show) pure (calculations M.! key)
    check (length (A.inputs calc) == 1) "unused callback leaked into runtime arguments"
    forM_ [False,True] $ \b -> do
      let owner = case head (A.inputs calc) of A.Named name -> name; _ -> error "missing carrier"
          con = head (A.variants (shapes M.! owner))
          value = R owner (M.fromList [("constructor",E (owner <> ".constructor-tag") (A.constructorSymbol con))
            ,(fst (head (A.payload con)),B b)])
          table = M.mapMaybe (either (const Nothing) Just) calculations
      check (evalWith table [value] (A.body calc) == value) "unused callback omission changed retained payload"
  forM_ [set "opaque" (Bool True),set "terminates" (Bool False),set "compiled" Null
        ,set "moduleParameters" Null] $ \change -> do
    let altered = inv {declarations = M.adjust change "passUnused" (declarations inv)}
    check (omitted altered "passUnused" == toJSON ([] :: [Int])
      && omitted altered "forwardUnused" == toJSON ([] :: [Int]))
      "missing metadata or opaque dependency allowed omission"
  let stored = inv {declarations = M.adjust (set "type" (signature [callback,callback]
        (ty "PhantomCallback" [v 1]))) "wrapUnused" (declarations inv)}
  -- The second function is a stored payload, not an unused module parameter.
  let storedPrepared = P.prepare stored
      storedInventory = P.inventory storedPrepared
      storedShapes = fst (A.discover storedInventory M.empty)
  storedKey <- maybe (fail (show (P.failures storedPrepared))) pure (M.lookup "PhantomCallback" (P.openRoots storedPrepared))
  storedShape <- maybe (fail "stored callback carrier missing") pure (M.lookup storedKey storedShapes)
  check ([t | c <- A.variants storedShape,(_,t) <- A.payload c] == [A.Callable [A.Boolean] A.Boolean])
    "stored function payload was erased or changed"

callableFieldChecks :: Inventory -> IO Text
callableFieldChecks base = do
  let callback = signature [named "Bool"] (named "Bool")
      box = set "constructor" (String "makeCallbackBox") $ set "fields" (toJSON (["callbackField"] :: [Text]))
        $ set "induction" (String "Just Inductive") $ declaration "CallbackBox" "record" (universeAt (level 0))
      ctor = set "family" (String "CallbackBox") $ declaration "makeCallbackBox" "constructor"
        (signature [callback] (named "CallbackBox"))
      projection = set "projection" (object ["proper" .= ("CallbackBox" :: Text),"index" .= (1 :: Int)])
        $ declaration "callbackField" "function" (signature [named "CallbackBox"] callback)
      applied = set "eliminations" (toJSON (array (get "eliminations" (variable 1 ["callbackField"]))
        ++ [application (variable 0 [])])) (variable 1 [])
      use = operation "useCallbackBox" ["CallbackBox","Bool"] "Bool" (done 2 applied)
      rebuild = operation "rebuildCallbackBox" ["CallbackBox"] "CallbackBox"
        (done 1 (constructor "makeCallbackBox" [variable 0 ["callbackField"]]))
      lambda binds body = object ["tag" .= ("lambda" :: Text)
        ,"abstraction" .= object ["binds" .= binds,"body" .= body]]
      capture = operation "captureValue" ["Bool"] "CallbackBox"
        (done 1 (constructor "makeCallbackBox" [lambda True (variable 1 [])]))
      unused = operation "captureUnused" ["Bool"] "CallbackBox"
        (done 1 (constructor "makeCallbackBox" [lambda False (variable 0 [])]))
      nested = operation "captureNested" ["Bool"] "CallbackBox"
        (done 1 (constructor "makeCallbackBox" [lambda True (call "useCallbackBox"
          [constructor "makeCallbackBox" [lambda True (variable 2 [])],variable 0 []] [])]))
      ds = [box,ctor,projection,use,rebuild,capture,unused,nested]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- ds]) (declarations base)
        ,modelRequirements = M.singleton "callbacks" (S.fromList [(string (get "name" d),
          if get "kind" d == String "function" then "behavior" else "structure") | d <- ds])}
      prepared = P.prepare inv
      expanded = P.inventory prepared
      shapes = fst (A.discover expanded M.empty)
      results = A.functions expanded M.empty shapes
  check (M.null (P.failures prepared)) (show (P.failures prepared))
  shape <- maybe (fail "callable record not admitted") pure (M.lookup "CallbackBox" shapes)
  check (A.isRecord shape && map snd (A.payload (head (A.variants shape))) == [A.Callable [A.Boolean] A.Boolean])
    "callable member changed its containing value carrier"
  sig <- either (fail . show) pure (P.signature inv projection)
  check (P.inputs sig == [P.Named "CallbackBox" []] && P.output sig == P.Callable [P.Named "Bool" []] (P.Named "Bool" []))
    "proper projection flattened its callable result into additional inputs"
  let identity = A.Calculation "fieldIdentity" [A.Boolean] A.Boolean (A.Input 0) []
      invert = A.Calculation "fieldInvert" [A.Boolean] A.Boolean
        (A.Conditional (A.Input 0) (A.Literal False) (A.Literal True)) []
      table = M.union (M.fromList [("fieldIdentity",identity),("fieldInvert",invert)])
        (M.mapMaybe (either (const Nothing) Just) results)
  forM_ ["useCallbackBox","rebuildCallbackBox","callbackField"] $ \s ->
    check (M.member s table) (show (s,M.lookup s results))
  forM_ [("fieldIdentity",id),("fieldInvert",not)] $ \(fn,expected) -> forM_ [False,True] $ \value -> do
    let record = R "CallbackBox" (M.singleton "callbackField" (Fn fn))
    check (evalWith table [record,B value] (A.body (table M.! "useCallbackBox")) == B (expected value))
      "projected callback invoked the wrong binding"
    check (evalWith table [record] (A.body (table M.! "rebuildCallbackBox")) == record)
      "reconstruction changed the stored callable reference"
  check ("ref calc 'callbackField' [1]" `Text.isInfixOf` Text.unlines (A.renderShapes id shapes))
    "callable member was emitted as an attribute or composite occurrence"
  check ("return ref calc 'result'" `Text.isInfixOf` Text.unlines
      (A.renderCalculation expanded shapes id (table M.! "callbackField")))
    "projection dropped its returned callback signature"
  forM_ ["captureValue","captureUnused","captureNested"] $ \s -> do
    calculation <- either (fail . show) pure (results M.! s)
    check ("{ in 'lambdaArgument" `Text.isInfixOf` Text.unlines (A.renderCalculation expanded shapes id calculation))
      "captured lambda did not become a native body expression"
    forM_ [False,True] $ \captured -> forM_ [False,True] $ \argument -> do
      let value = evalWith table [B captured] (A.body calculation)
      check (evalWith table [value,B argument] (A.body (table M.! "useCallbackBox")) == B captured)
        "nested or unused lambda binder changed a captured value"
  forM_ [lambda True (constructor "red" []),lambda True (variable 9 []),lambda True (lambda True (variable 0 []))] $ \badBody -> do
    let invalid = inv {declarations = M.insert "captureValue"
          (set "compiled" (done 1 (constructor "makeCallbackBox" [badBody])) capture) (declarations inv)}
    check (not (T.complete (T.generate invalid))) "ill-typed or unbound captured lambda admitted"
  forM_ [set "index" (Number 2),set "proper" (String "WrongOwner")] $ \change -> do
    let invalid = inv {declarations = M.adjust (set "projection" (change (get "projection" projection))) "callbackField" (declarations inv)}
    check (M.notMember "CallbackBox" (fst (A.discover (P.inventory (P.prepare invalid)) M.empty)))
      "malformed proper callable projection admitted"
  let generated = T.generate inv
  check (T.complete generated) (show (T.diagnostics generated))
  pure (Text.replace "package 'AgdaModel' {" "package 'CallableFieldFixture' {" (T.modelText generated))

-- Renamed compiler-shaped declarations: a stored callback and a dependent
-- evidence callback whose result retains an application of the first field.
-- No project-specific dispatch or source wrappers can satisfy this fixture.
dependentCallableChecks :: Inventory -> IO Text
dependentCallableChecks base = do
  let indexed = declaration "IndexedValue" "datatype" (signature [named "Bool"] (universeAt (level 0)))
      eqType = set "parameters" (Number 1) $ declaration "ScopedEvidence" "datatype"
        (signature [universeAt (level 0),object ["term" .= variable 0 []],object ["term" .= variable 1 []]] (universeAt (level 0)))
      scoped = base {declarations = M.union (M.fromList [("IndexedValue",indexed),("ScopedEvidence",eqType)]) (declarations base)}
      boolean = P.Named "Bool" []
      fibre = P.Named "IndexedValue" [P.Runtime boolean (P.IndexInput 0)]
      environment = [Just (P.Runtime fibre (P.IndexInput 1)),Just (P.Runtime boolean (P.IndexInput 0))]
      evidenceType = call "ScopedEvidence" [call "IndexedValue" [variable 1 []] [],variable 0 [],variable 0 []] []
  scopedType <- either (fail . show) pure (P.readType scoped environment evidenceType)
  check (scopedType == P.Named "ScopedEvidence" [fibre,P.Runtime fibre (P.IndexInput 1),P.Runtime fibre (P.IndexInput 1)])
    "index substitution captured an index inside the caller's static type argument"
  dependent <- either (fail . show) pure (P.readType scoped []
    (get "term" (signature [named "Bool"] (object ["term" .= call "IndexedValue" [variable 0 []] []]))))
  check (dependent == P.Callable [boolean] (P.Named "IndexedValue" [P.Runtime boolean (P.IndexArgument 0)]))
    "callback argument was confused with an enclosing runtime index"
  let v i = variable i []
      ty s xs = object ["term" .= call s xs []]
      applied f x = set "eliminations" (toJSON (array (get "eliminations" f) ++ [application x])) f
      callback = signature [named "Bool"] (named "Bool")
      evidence fn = signature [named "Bool"] (ty "Receipt" [applied fn (v 0),v 0])
      receipt = set "constructors" (toJSON (["receipt"] :: [Text])) $
        declaration "Receipt" "datatype" (signature [named "Bool",named "Bool"] (universeAt (level 0)))
      receiptCtor = set "family" (String "Receipt") $ declaration "receipt" "constructor"
        (signature [named "Bool"] (ty "Receipt" [v 0,v 0]))
      copiedReceipt = set "moduleInstanceCopy" (Bool True) $ set "canonicalConstructor" (String "receipt")
        $ set "name" (String "copiedReceipt") $ set "displayName" (String "copiedReceipt") receiptCtor
      box = set "constructor" (String "bindContract") $ set "fields" (toJSON (["transform","witness"] :: [Text]))
        $ set "induction" (String "Just Inductive") $ declaration "ContractBox" "record" (universeAt (level 0))
      ctor = set "family" (String "ContractBox") $ declaration "bindContract" "constructor"
        (signature [callback,evidence (v 1)] (named "ContractBox"))
      projection s out = set "projection" (object ["proper" .= ("ContractBox" :: Text),"index" .= (1 :: Int)])
        $ declaration s "function" (signature [named "ContractBox"] out)
      transform = projection "transform" callback
      witness = projection "witness" (evidence (variable 1 ["transform"]))
      invoke = set "type" (signature [named "ContractBox",named "Bool"]
          (ty "Receipt" [applied (variable 1 ["transform"]) (v 0),v 0]))
        $ operation "invokeWitness" [] "Bool" (done 2 (applied (variable 1 ["witness"]) (v 0)))
      direct = set "type" (signature [signature [named "Bool"] (ty "Receipt" [v 0,v 0]),named "Bool"]
          (ty "Receipt" [v 0,v 0]))
        $ operation "invokeDependent" [] "Bool" (done 2 (applied (v 1) (v 0)))
      rebuild = operation "rebindContract" ["ContractBox"] "ContractBox"
        (done 1 (constructor "bindContract" [variable 0 ["transform"],variable 0 ["witness"]]))
      make = set "type" (signature [named "Bool"] (ty "Receipt" [v 0,v 0]))
        $ operation "makeCopiedReceipt" [] "Bool" (done 1 (constructor "copiedReceipt" [v 0]))
      many = signature [named "Bool",named "Bool",ty "Receipt" [v 1,v 0]] (ty "Receipt" [v 2,v 1])
      invokeMany = set "type" (signature [many,named "Bool",named "Bool",ty "Receipt" [v 1,v 0]]
          (ty "Receipt" [v 2,v 1])) $ operation "invokeMany" [] "Bool"
          (done 4 (applied (applied (applied (v 3) (v 2)) (v 1)) (v 0)))
      multiBox = set "constructor" (String "bindMany") $ set "fields" (toJSON (["manyMember"] :: [Text]))
        $ set "induction" (String "Just Inductive") $ declaration "MultiBox" "record" (universeAt (level 0))
      multiCtor = set "family" (String "MultiBox") $ declaration "bindMany" "constructor" (signature [many] (named "MultiBox"))
      multiField = set "projection" (object ["proper" .= ("MultiBox" :: Text),"index" .= (1 :: Int)])
        $ declaration "manyMember" "function" (signature [named "MultiBox"] many)
      invokeField = set "type" (signature [named "MultiBox",named "Bool",named "Bool",ty "Receipt" [v 1,v 0]]
          (ty "Receipt" [v 2,v 1])) $ operation "invokeManyField" [] "Bool"
          (done 4 (applied (applied (applied (variable 3 ["manyMember"]) (v 2)) (v 1)) (v 0)))
      forwarded = set "name" (String "forwardMany") $ set "displayName" (String "forwardMany")
        $ set "compiled" (done 4 (call "invokeMany" [v 3,v 2,v 1,v 0] [])) invokeMany
      ds = [receipt,receiptCtor,copiedReceipt,box,ctor,transform,witness,invoke,direct,rebuild,make,
            invokeMany,multiBox,multiCtor,multiField,invokeField,forwarded]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- ds]) (declarations base)
        ,modelRequirements = M.singleton "dependent-callbacks" (S.fromList [(string (get "name" d),
          if get "kind" d == String "function" then "behavior" else "structure")
          | d <- ds,get "name" d /= String "copiedReceipt"])}
      prepared = P.prepare inv
      expanded = P.inventory prepared
      (shapes,errors) = A.discover expanded M.empty
      results = A.functions expanded M.empty shapes
  check (M.null (P.failures prepared)) (show (P.failures prepared))
  check (M.member "ContractBox" shapes) (show errors)
  table <- traverse (either (fail . show) pure) results
  forM_ ["invokeWitness","invokeDependent","rebindContract","invokeMany","invokeManyField","forwardMany"] $ \s ->
    check (M.member s table) (show (s,results))
  let identity = A.Calculation "receiptIdentity" [A.Boolean] A.Boolean (A.Input 0) []
      certify = A.Calculation "certify" [A.Boolean] (A.Fibre "Receipt" [A.Input 0,A.Input 0])
        (A.Construct "Receipt" [("constructor",A.Enumeration "Receipt.constructor-tag" "receipt")
          ,("Receipt.index0",A.Input 0),("Receipt.index1",A.Input 0),("receipt.payload0",A.Input 0)]) []
      identityMany = A.Calculation "identityMany" [A.Boolean,A.Boolean,A.Fibre "Receipt" [A.Input 0,A.Input 1]]
        (A.Fibre "Receipt" [A.Input 0,A.Input 1]) (A.Input 2) []
      runtime = M.union (M.fromList [("receiptIdentity",identity),("certify",certify),("identityMany",identityMany)]) table
      record = R "ContractBox" (M.fromList [("transform",Fn "receiptIdentity"),("witness",Fn "certify")])
  forM_ [False,True] $ \b -> do
    let expected = evalWith runtime [B b] (A.body certify)
    check (evalWith runtime [record,B b] (A.body (table M.! "invokeWitness")) == expected)
      "dependent callback discarded or changed its evidence value"
    check (evalWith runtime [Fn "certify",B b] (A.body (table M.! "invokeDependent")) == expected)
      "direct callback failed to instantiate its result indices"
    check (evalWith runtime [B b] (A.body (table M.! "makeCopiedReceipt")) == expected)
      "module-copy constructor retained an unadmitted alias head"
    forM_ ["invokeMany","forwardMany"] $ \s ->
      check (evalWith runtime [Fn "identityMany",B b,B b,expected] (A.body (table M.! s)) == expected)
        "multiargument callback lost its complete dependent evidence result"
    check (evalWith runtime [R "MultiBox" (M.singleton "manyMember" (Fn "identityMany")),B b,B b,expected]
      (A.body (table M.! "invokeManyField")) == expected) "stored multiargument callback changed its result"
  check (evalWith runtime [record] (A.body (table M.! "rebindContract")) == record)
    "reconstruction changed evidence-producing callback bindings"
  let wrong = inv {declarations = M.adjust (set "compiled" (done 2
        (applied (variable 1 ["witness"]) (constructor "red" [])))) "invokeWitness" (declarations inv)}
      wrongPrepared = P.prepare wrong
      wrongInventory = P.inventory wrongPrepared
  check (M.member "invokeWitness" (P.failures wrongPrepared)
    || maybe True isLeft (M.lookup "invokeWitness" (A.functions wrongInventory M.empty (fst (A.discover wrongInventory M.empty)))))
    "wrong callback argument admitted"
  forM_ [applied (v 3) (v 2),applied (applied (applied (v 3) (v 1)) (v 2)) (v 0),
         applied (applied (applied (applied (v 3) (v 2)) (v 1)) (v 0)) (v 0)] $ \term -> do
    let bad = P.prepare (inv {declarations = M.adjust (set "compiled" (done 4 term)) "invokeMany" (declarations inv)})
        checked = P.inventory bad
    check (M.member "invokeMany" (P.failures bad) || maybe True isLeft
      (M.lookup "invokeMany" (A.functions checked M.empty (fst (A.discover checked M.empty)))))
      "partial, overapplied or wrongly indexed callback admitted"
  let generated = T.generate inv
  check (T.complete generated) (show (T.diagnostics generated))
  check ("'Receipt.index0'" `Text.isInfixOf` T.modelText generated
    && "ref calc 'witness'" `Text.isInfixOf` T.modelText generated)
    "dependent evidence callback signature missing from emitted model"
  let nativeCallback = object ["term" .= object ["tag" .= ("native-callable" :: Text)
        ,"binds" .= True,"input" .= named "Bool","result" .= named "Bool"]]
      functionIndexed = set "constructors" (toJSON (["functionIndex"] :: [Text]))
        $ declaration "FunctionIndexed" "datatype" (signature [nativeCallback] (universeAt (level 0)))
      functionIndex = set "family" (String "FunctionIndexed") $ declaration "functionIndex" "constructor"
        (signature [nativeCallback] (ty "FunctionIndexed" [v 0]))
      functionRelation = set "nativeFamily" (Number 0) $ set "familyDomains" (toJSON [nativeCallback])
        $ declaration "FunctionRelation" "native-family-parameter" (universeAt (level 0))
      unsupported = base {declarations = M.union (M.fromList
        [(string (get "name" d),d) | d <- [functionIndexed,functionIndex,functionRelation]]) (declarations base)
        ,modelRequirements = M.singleton "function-indices" (S.singleton ("FunctionIndexed","structure"))}
      (unsupportedShapes,unsupportedErrors) = A.discover unsupported M.empty
  forM_ ["FunctionIndexed","FunctionRelation"] $ \s -> do
    check (M.notMember s unsupportedShapes) "function-valued family index emitted as a data attribute"
    check (maybe False (Text.isInfixOf "Function-valued family indices" . Text.pack . show)
      (M.lookup s unsupportedErrors)) "function-valued family index lacks an explicit refusal"
  pure (Text.replace "package 'AgdaModel' {" "package 'DependentCallableFixture' {" (T.modelText generated))

-- Stored type/family fields are runtime bindings, distinct from a record's
-- declared parameters. The member keeps both that binding and its payload.
schemaRecordChecks :: Inventory -> IO Text
schemaRecordChecks base = do
  check (either (const True) (const False) (P.readType base [] (object
    ["tag" .= ("sort" :: Text),"sort" .= object ["tag" .= ("universe" :: Text)
      ,"kind" .= ("UProp" :: Text),"level" .= level 0]])))
    "proof-irrelevant universe admitted by the stored Set schema rule"
  let boolean = P.Named "Bool" []
      indexed i = P.Named "Indexed" [P.Runtime boolean i]
      wrapper i = P.Named "Wrapper" [indexed i]
  check (P.typeKey (wrapper (P.IndexArgument 0)) == P.typeKey (wrapper (P.IndexInput 4)))
    "callback-local static carrier argument was not captured like a caller-local argument"
  check (P.typeKey (P.Named "Wrapper" [P.Callable [boolean] (indexed (P.IndexArgument 0))])
      /= P.typeKey (P.Named "Wrapper" [P.Callable [boolean] (indexed (P.IndexInput 0))]))
    "bound callback argument was confused with a captured outer value"
  let term t = object ["term" .= t]
      v i = variable i []
      apply f x = set "eliminations" (toJSON (array (get "eliminations" f) ++ [application x])) f
      record name ctor fields = set "constructor" (String ctor) $ set "fields" (toJSON (fields :: [Text]))
        $ set "induction" (String "Just Inductive") $ declaration name "record" (universeAt (level 1))
      field owner name result = set "projection" (object ["proper" .= owner,"index" .= (1 :: Int)])
        $ declaration name "function" (signature [named owner] result)
      box = record "SchemaBox" "schemaBox" ["schemaType","schemaPayload"]
      ctor = set "family" (String "SchemaBox") $ declaration "schemaBox" "constructor"
        (signature [universeAt (level 0),term (v 0)] (named "SchemaBox"))
      typ = field "SchemaBox" "schemaType" (universeAt (level 0))
      value = field "SchemaBox" "schemaPayload" (term (variable 0 ["schemaType"]))
      rebuild = operation "rebuildSchemaBox" ["SchemaBox"] "SchemaBox"
        (done 1 (constructor "schemaBox" [variable 0 ["schemaType"],variable 0 ["schemaPayload"]]))
      familyType = signature [named "Bool"] (universeAt (level 0))
      wrapped value = object ["term" .= call "SchemaWrapper" [value] []]
      wrapper = set "parameters" (Number 1) $ set "type" (signature [universeAt (level 0)] (universeAt (level 0)))
        $ record "SchemaWrapper" "schemaWrapper" ["wrappedPayload"]
      wrapperCtor = set "parameters" (Number 1) $ set "family" (String "SchemaWrapper")
        $ declaration "schemaWrapper" "constructor" (signature [universeAt (level 0),term (v 0)] (wrapped (v 1)))
      wrapperProjection = set "projection" (object ["proper" .= ("SchemaWrapper" :: Text),"index" .= (2 :: Int)])
        $ declaration "wrappedPayload" "function" (signature [universeAt (level 0),wrapped (v 0)] (term (v 1)))
      receipt familyTerm = signature [named "Bool"] (wrapped (apply familyTerm (v 0)))
      family = record "FamilyBox" "familyBox" ["storedFamily","otherFamily","familyIndex","familyPayload","familyReceipt"]
      familyCtor = set "family" (String "FamilyBox") $ declaration "familyBox" "constructor"
        (signature [familyType,familyType,named "Bool",term (apply (v 2) (v 0)),receipt (v 4)] (named "FamilyBox"))
      stored = field "FamilyBox" "storedFamily" familyType
      other = field "FamilyBox" "otherFamily" familyType
      index = field "FamilyBox" "familyIndex" (named "Bool")
      payload = field "FamilyBox" "familyPayload" (term (apply (variable 0 ["storedFamily"]) (variable 0 ["familyIndex"])))
      receiptProjection = field "FamilyBox" "familyReceipt" (receipt (variable 1 ["storedFamily"]))
      rebuildFamily = operation "rebuildFamilyBox" ["FamilyBox"] "FamilyBox"
        (done 1 (constructor "familyBox" [variable 0 [f] | f <- ["storedFamily","otherFamily","familyIndex","familyPayload","familyReceipt"]]))
      dependentFields = ["dependentType","differentType","dependentFamily","dependentIndex","dependentEvidence"]
      dependent = record "DependentSchemaBox" "dependentSchemaBox" dependentFields
      dependentCtor = set "family" (String "DependentSchemaBox") $ declaration "dependentSchemaBox" "constructor"
        (signature [universeAt (level 0),universeAt (level 0),signature [term (v 1)] (universeAt (level 0))
          ,term (v 2),term (apply (v 1) (v 0))] (named "DependentSchemaBox"))
      dependentType = field "DependentSchemaBox" "dependentType" (universeAt (level 0))
      differentType = field "DependentSchemaBox" "differentType" (universeAt (level 0))
      dependentFamily = field "DependentSchemaBox" "dependentFamily"
        (signature [term (variable 0 ["dependentType"])] (universeAt (level 0)))
      dependentIndex = field "DependentSchemaBox" "dependentIndex" (term (variable 0 ["dependentType"]))
      dependentEvidence = field "DependentSchemaBox" "dependentEvidence"
        (term (apply (variable 0 ["dependentFamily"]) (variable 0 ["dependentIndex"])))
      rebuildDependent = operation "rebuildDependentSchemaBox" ["DependentSchemaBox"] "DependentSchemaBox"
        (done 1 (constructor "dependentSchemaBox" [variable 0 [f] | f <- dependentFields]))
      produced = record "ProducedSchema" "producedSchema" ["producedFamily"]
      producedCtor = set "family" (String "ProducedSchema") $ declaration "producedSchema" "constructor"
        (signature [familyType] (named "ProducedSchema"))
      producedField = field "ProducedSchema" "producedFamily" familyType
      indexedFamily = set "parameters" (Number 1)
        $ set "type" (signature [named "Bool"] (universeAt (level 0)))
        $ record "IndexedPayload" "indexedPayload" ["payloadFlag"]
      indexedCtor = set "parameters" (Number 1) $ set "family" (String "IndexedPayload")
        $ declaration "indexedPayload" "constructor"
          (signature [named "Bool",named "Bool"] (term (call "IndexedPayload" [v 1] [])))
      indexedField = set "projection" (object ["proper" .= ("IndexedPayload" :: Text),"index" .= (2 :: Int)])
        $ declaration "payloadFlag" "function"
          (signature [named "Bool",term (call "IndexedPayload" [v 0] [])] (named "Bool"))
      produce = operation "produceSchema" [] "ProducedSchema"
        (done 0 (constructor "producedSchema" [call "IndexedPayload" [] []]))
      ds = [box,ctor,typ,value,rebuild,wrapper,wrapperCtor,wrapperProjection,family,familyCtor,stored,other,index,payload,receiptProjection,rebuildFamily
        ,dependent,dependentCtor,dependentType,differentType,dependentFamily,dependentIndex,dependentEvidence,rebuildDependent
        ,produced,producedCtor,producedField,indexedFamily,indexedCtor,indexedField,produce]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- ds]) (declarations base)
        ,modelRequirements = M.singleton "schema-fields" (S.fromList [(string (get "name" d),
          if get "kind" d == String "function" then "behavior" else "structure") | d <- ds])}
      prepared = P.prepare inv
      expanded = P.inventory prepared
      (shapes,errors) = A.discover expanded M.empty
      calculations = A.functions expanded M.empty shapes
  sig <- either (fail . show) pure (P.signature inv ctor)
  check (P.parameters sig == 0 && length (P.inputs sig) == 2) "stored type field was mistaken for a declaration parameter"
  check (M.null (P.failures prepared)) (show (P.failures prepared))
  check (all (`M.member` shapes) ["SchemaBox","FamilyBox","DependentSchemaBox"]) (show errors)
  forM_ ["rebuildSchemaBox","rebuildFamilyBox","rebuildDependentSchemaBox","produceSchema"] $ \symbol ->
    check (maybe False (either (const False) (const True)) (M.lookup symbol calculations)) (show (symbol,calculations))
  let bad = inv {declarations = M.adjust (set "type" (signature [named "FamilyBox"]
        (term (apply (variable 0 ["otherFamily"]) (variable 0 ["familyIndex"]))))) "familyPayload" (declarations inv)}
      wrong = P.inventory (P.prepare bad)
  check (M.notMember "FamilyBox" (fst (A.discover wrong M.empty)))
    "projection from a different stored family was accepted"
  let swapped = inv {declarations = M.adjust (set "type" (signature [named "DependentSchemaBox"]
        (signature [term (variable 0 ["differentType"])] (universeAt (level 0))))) "dependentFamily" (declarations inv)}
  check (M.notMember "DependentSchemaBox" (fst (A.discover (P.inventory (P.prepare swapped)) M.empty)))
    "stored family accepted the wrong captured type field"
  let recursive = inv {declarations = M.adjust (set "type"
        (signature [named "Bool",term (call "IndexedPayload" [v 0] [])]
          (term (call "IndexedPayload" [v 1] [])))) "indexedPayload" (declarations inv)}
  check (maybe False (Text.isInfixOf "nonrecursive record family" . Text.pack . show)
    (M.lookup "produceSchema" (P.failures (P.prepare recursive))))
    "computed schema attempted to enumerate a recursive record family"
  let callback = signature [named "Bool"] (named "Bool")
      unbounded = inv {declarations = M.adjust (set "type"
          (signature [named "Bool",callback] (term (call "IndexedPayload" [v 1] [])))) "indexedPayload"
        $ M.adjust (set "type" (signature [named "Bool",term (call "IndexedPayload" [v 0] [])] callback))
          "payloadFlag" (declarations inv)}
      unboundedPrepared = P.prepare unbounded
      unboundedInventory = P.inventory unboundedPrepared
      unboundedShapes = fst (A.discover unboundedInventory M.empty)
      unboundedCalculations = A.functions unboundedInventory M.empty unboundedShapes
  check (M.null (P.failures unboundedPrepared)) (show (P.failures unboundedPrepared))
  check (maybe False (either (Text.isInfixOf "Computed schema" . Text.pack . show) (const False))
    (M.lookup "produceSchema" unboundedCalculations))
    "computed schema invented an extent of arbitrary callback values"
  let generated = T.generate inv
  check (T.complete generated) (show (T.diagnostics generated))
  check ("->exists" `Text.isInfixOf` T.modelText generated) "stored family membership constraint missing"
  check (Trace.validate (T.modelText generated) (get "sourceCorrespondence" (T.correspondence generated)) == Right ())
    "stored schema generated provenance does not resolve"
  pure (Text.replace "package 'AgdaModel' {" "package 'SchemaRecordFixture' {" (T.modelText generated))

-- Recursive lookups with indexed inputs reduce only under justified branch
-- facts. Different caller expressions must meet at the same residual call.
indexedLookupChecks :: Inventory -> IO ()
indexedLookupChecks base = do
  let ty s args = object ["term" .= call s args []]
      v i = variable i []
      family s cs = set "constructors" (toJSON (cs :: [Text])) $
        declaration s "datatype" (signature [named "Bool"] (universeAt (level 0)))
      cursor = set "induction" (String "Inductive") $ set "sourceModule" (String "CheckedLookup") $
        family "Cursor" ["end","more"]
      flag = family "LookupFlag" ["lookupFlag"]
      ctor s owner ins out = set "family" (String owner) $ declaration s "constructor" (signature ins out)
      end = ctor "end" "Cursor" [named "Bool"] (ty "Cursor" [v 0])
      more = ctor "more" "Cursor" [named "Bool",ty "Cursor" [v 0]] (ty "Cursor" [v 1])
      flagCtor = ctor "lookupFlag" "LookupFlag" [named "Bool"] (ty "LookupFlag" [v 0])
      lookupCall b x = call "lookupIndex" [b,x] []
      safe = set "opaque" (Bool False) . set "terminates" (Bool True) . set "sourceModule" (String "CheckedLookup")
      op s ins out tree = safe $ set "type" (signature ins out) $ operation s [] "Bool" tree
      lookupDef = op "lookupIndex" [named "Bool",ty "Cursor" [v 0]] (named "Bool")
        (split 1 [("end",1,done 2 (v 0)),("more",2,done 3 (lookupCall (v 1) (v 0)))])
      build = op "buildLookup" [named "Bool",ty "Cursor" [v 0]]
        (ty "LookupFlag" [lookupCall (v 1) (v 0)])
        (split 1 [("end",1,done 2 (constructor "lookupFlag" [v 0]))
          ,("more",2,done 3 (call "buildLookup" [v 1,v 0] []))])
      declarations' = [cursor,end,more,flag,flagCtor,lookupDef,build]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- declarations']) (declarations base)
        ,document = set "checking" (toJSON [object ["module" .= ("CheckedLookup" :: Text),"safe" .= True
            ,"terminationCheck" .= True,"positivityCheck" .= True]]) (document base)
        ,modelRequirements = M.singleton "lookup" (S.fromList [(string (get "name" d),
            if get "kind" d == String "function" then "behavior" else "structure") | d <- declarations'])}
      (shapes,shapeErrors) = A.discover inv M.empty
      calculations = A.functions inv M.empty shapes
      value b 0 = R "Cursor" (M.fromList [("constructor",E "Cursor.constructor-tag" "end")
        ,("Cursor.index0",B b),("end.payload0",B b)])
      value b n = R "Cursor" (M.fromList [("constructor",E "Cursor.constructor-tag" "more")
        ,("Cursor.index0",B b),("more.payload0",B b),("more.payload1",value b (n-1))])
  check (M.member "Cursor" shapes && M.member "LookupFlag" shapes) (show shapeErrors)
  table <- traverse (either (fail . show) pure) calculations
  forM_ [False,True] $ \b -> forM_ [0..8 :: Int] $ \n -> do
    let expected = R "LookupFlag" (M.fromList [("constructor",E "LookupFlag.constructor-tag" "lookupFlag")
          ,("LookupFlag.index0",B b),("lookupFlag.payload0",B b)])
    check (evalWith table [B b,value b n] (A.body (table M.! "buildLookup")) == expected)
      "computed indexed lookup lost its complete result"
  forM_ [set "opaque" (Bool True),set "terminates" (Bool False),set "compiled" Null] $ \change -> do
    let invalid = inv {declarations = M.adjust change "lookupIndex" (declarations inv)}
    check (isLeft (A.functions invalid M.empty (fst (A.discover invalid M.empty)) M.! "buildLookup"))
      "opaque, unchecked or absent recursive lookup justified an index"
  let wrong = inv {declarations = M.adjust (set "compiled" (split 1
        [("end",1,done 2 (constructor "lookupFlag" [constructor "false" []]))
        ,("more",2,done 3 (call "buildLookup" [v 1,v 0] []))])) "buildLookup" (declarations inv)}
  check (isLeft (A.functions wrong M.empty (fst (A.discover wrong M.empty)) M.! "buildLookup"))
    "unknown computed index equality was guessed"

-- Computed finite indices require checked bodies, not merely signatures.
computedChecks :: Inventory -> IO ()
computedChecks base = do
  let piType binds a b = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= a,"info" .= info]
        ,"codomain" .= object ["binds" .= binds,"body" .= b]]]
      boolPi = piType True (named "Bool")
      ty s args = object ["term" .= call s args []]
      invert x = call "invertIndex" [x] []
      namedIndex x = call "namedIndex" [x] []
      true = constructor "true" []
      false = constructor "false" []
      function s t tree = set "compiled" tree $ set "sourceSyntax" (toJSON [object []]) $ declaration s "function" t
      inversion = operation "invertIndex" ["Bool"] "Bool"
        (split 0 [("true",0,done 0 false),("false",0,done 0 true)])
      toneIndex = operation "namedIndex" ["Bool"] "Tone"
        (split 0 [("true",0,done 0 (constructor "red" [])),("false",0,done 0 (constructor "blue" []))])
      chain = operation "chainIndex" ["Bool"] "Tone" (done 1 (namedIndex (invert (variable 0 []))))
      flags = set "constructors" (toJSON (["computedFlag"] :: [Text]))
        $ declaration "ComputedFlag" "datatype" (boolPi (universeAt (level 0)))
      flagCtor = declaration "computedFlag" "constructor" (boolPi (ty "ComputedFlag" [variable 0 []]))
      family = set "constructors" (toJSON (["computedMember"] :: [Text]))
        $ declaration "ComputedFamily" "datatype" (piType False (named "Tone") (universeAt (level 0)))
      member = declaration "computedMember" "constructor"
        (boolPi (piType False (ty "ComputedFlag" [invert (variable 0 [])])
          (ty "ComputedFamily" [call "chainIndex" [variable 0 []] []])))
      make = function "makeComputed" (boolPi (ty "ComputedFamily" [namedIndex (invert (variable 0 []))]))
        (done 1 (constructor "computedMember" [variable 0 [],constructor "computedFlag" [invert (variable 0 [])]]))
      consume = function "consumeComputed" (boolPi
        (piType False (ty "ComputedFlag" [invert (variable 0 [])]) (ty "ComputedFlag" [invert (variable 0 [])])))
        (split 1 [("computedFlag",1,done 2 (constructor "computedFlag" [variable 0 []]))])
      fixed = function "fixedComputed" (piType False (named "Bool") (ty "ComputedFlag" [invert false]))
        (done 1 (constructor "computedFlag" [true]))
      branch = function "branchComputed" (boolPi (ty "ComputedFlag" [invert (variable 0 [])]))
        (split 0 [("true",0,done 0 (constructor "computedFlag" [false]))
          ,("false",0,done 0 (constructor "computedFlag" [true]))])
      alias = function "signatureOnlyComputed" (boolPi
        (piType False (ty "ComputedFlag" [invert (variable 0 [])]) (ty "ComputedFlag" [invert (variable 0 [])])))
        (done 2 (variable 0 []))
      choice = set "constructors" (toJSON (["computedOff","computedOn"] :: [Text]))
        $ declaration "ComputedChoice" "datatype" (boolPi (universeAt (level 0)))
      off = declaration "computedOff" "constructor" (ty "ComputedChoice" [false])
      on = declaration "computedOn" "constructor" (ty "ComputedChoice" [true])
      fixedChoice = function "computedChoiceRead" (piType False (ty "ComputedChoice" [invert false]) (named "Bool"))
        (split 0 [("computedOn",0,done 0 true)])
      additions = [inversion,toneIndex,chain,flags,flagCtor,family,member,make,consume,fixed,branch,alias
        ,choice,off,on,fixedChoice]
      defs = M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
      added = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      inv = base {declarations = defs,modelRequirements = M.map (`S.union` added) (modelRequirements base)}
      finite = M.singleton "Tone" (F.Domain "Tone" ["red","blue"])
      (shapes,errors) = A.discover inv finite
      results = A.functions inv finite shapes
      table = M.mapMaybe (either (const Nothing) Just) results
      calculate s args = evalWith table args (A.body (table M.! s))
      flagged b = R "ComputedFlag" (M.fromList [("constructor",E "ComputedFlag.constructor-tag" "computedFlag")
        ,("ComputedFlag.index0",B b),("computedFlag.payload0",B b)])
      bad d message = do
        let changed = inv {declarations = M.insert (string (get "name" d)) d defs}
        check (not (T.complete (T.generate changed))) message
      generated = T.generate inv
  check (M.null errors) (show errors)
  check (T.complete generated) (show (T.diagnostics generated))
  forM_ [False,True] $ \b -> do
    let f = flagged (not b)
        value = R "ComputedFamily" (M.fromList
          [("constructor",E "ComputedFamily.constructor-tag" "computedMember")
          ,("ComputedFamily.index0",E "Tone" (if b then "blue" else "red"))
          ,("computedMember.payload0",B b),("computedMember.payload1",f)])
    check (calculate "makeComputed" [B b] == value) "computed constructor index changed"
    check (calculate "consumeComputed" [B b,f] == f) "computed branch equality was lost during reconstruction"
    check (calculate "branchComputed" [B b] == f) "finite input branch did not reduce its index helper"
    check (calculate "fixedComputed" [B b] == flagged True) "literal index calculation did not reduce"
  check (calculate "computedChoiceRead" [R "ComputedChoice" (M.fromList
    [("constructor",E "ComputedChoice.constructor-tag" "computedOn"),("ComputedChoice.index0",B True)])] == B True)
    "computed closed index did not eliminate an impossible branch"
  bad (set "compiled" (split 0 [("computedOff",0,done 0 false)]) fixedChoice)
    "computed closed index omitted its possible branch"
  bad (set "compiled" (done 1 (call "chainIndex" [variable 0 []] [])) toneIndex)
    "mutually recursive index helpers accepted"
  bad (operation "invertIndex" ["Pair"] "Bool" (done 1 (variable 0 ["flag"])))
    "nonfinite helper domain justified a computed index"
  bad (set "type" (boolPi (piType False (ty "ComputedFlag" [invert (variable 0 [])])
    (ty "ComputedFlag" [variable 0 []]))) consume) "computed branch equality was inverted without evidence"
  check (S.member "invertIndex" (A.dependencies (table M.! "signatureOnlyComputed")))
    "signature-only calculation dependency missing"
  check ("'chainIndex'(" `Text.isInfixOf` T.modelText generated) "computed index was erased from native output"
  bad (set "compiled" Null inversion) "signature-only helper justified an index"
  bad (set "opaque" (Bool True) inversion) "opaque helper justified an index"
  bad (set "compiled" (done 1 (invert (variable 0 []))) inversion) "recursive index helper was accepted"
  bad (set "compiled" (split 0 [("true",0,done 0 false)]) inversion) "incomplete index helper admitted"
  bad (set "compiled" (done 1 (call "unknownIndexHelper" [variable 0 []] [])) inversion)
    "unsupported helper dependency admitted"
  bad (set "type" (boolPi (ty "ComputedFamily" [invert (variable 0 [])])) make) "wrong computed index domain admitted"
  bad (set "compiled" (done 1 (constructor "computedFlag" [false])) fixed) "unequal computed literal index accepted"
  bad (set "type" (boolPi (ty "ComputedFlag" [variable 0 []])) branch) "unknown index equality guessed"
  bad (set "type" (boolPi (ty "ComputedFlag" [call "invertIndex" [] []])) branch) "partial index helper admitted"
  bad (set "type" (boolPi (ty "ComputedFlag" [invert (constructor "red" [])])) branch)
    "index helper accepted wrong argument domain"

-- Exercise the real rule failures and complete report assembly, rather than
-- classifying message strings. Changing wording must never change a code.
diagnosticChecks :: Inventory -> M.Map Text F.Domain -> M.Map Text A.Shape -> IO ()
diagnosticChecks inv finite shapes = do
  let source = object ["file" .= ("Public.agda" :: Text), "line" .= (7 :: Int)]
      annotate = set "sourceSyntax" (toJSON [source]) . set "sourceModule" (String "Public")
      badSyntax = annotate $ operation "syntax" ["Bool"] "Bool"
        (done 1 (object ["tag" .= ("lambda" :: Text)]))
      badSemantics = annotate $ operation "semantics" ["Bool"] "Bool"
        (set "fallThrough" (Bool True) (split 0
          [("true",0,done 0 (constructor "true" [])),("false",0,done 0 (constructor "false" []))]))
      badRepresentation = annotate $ operation "representation" ["MissingCarrier"] "Bool"
        (done 1 (constructor "true" []))
      cases = [(badSyntax,D.Syntax),(badSemantics,D.Semantics),(badRepresentation,D.Representation)]
      extend additions = inv
        { declarations = M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations inv)
        , modelRequirements = M.insert "also-affected"
            (S.fromList [(string (get "name" d),"behavior") | d <- additions])
            (M.map (S.union (S.fromList [(string (get "name" d),"behavior") | d <- additions])) (modelRequirements inv)) }
      expectedCode c = String (D.code (D.refusal c "wording-independent"))
  check (T.complete (T.generate inv)) "diagnostic baseline is incomplete"
  forM_ cases $ \(definition,kind) -> do
    case A.function inv finite shapes definition of
      Left reason -> check (D.category reason == kind) (show reason)
      Right _ -> fail "unsupported diagnostic case translated"
    let symbol = string (get "name" definition)
        caller = annotate $ operation "caller" ["Bool"] "Bool" (done 1 (call symbol [variable 0 []] []))
        additions = if kind == D.Representation then [definition] else [definition,caller]
        altered = extend additions
        results = A.functions altered finite shapes
    forM_ additions $ \d -> case M.lookup (string (get "name" d)) results of
      Just (Left reason) -> check (D.category reason == kind) "callee refusal category lost"
      other -> fail (show other)
    let generated = T.generate altered
        report = T.correspondence generated
        unresolved = [o | o <- array (get "obligations" report), get "status" o == String "textual"]
        problems = T.diagnostics generated
        coverage = get "coverage" report
    check (not (T.complete generated) && length problems == length additions
      && length unresolved == length problems) "diagnostic categories changed refusal accounting"
    check (get "dischargedObligations" coverage ==
      Number (fromIntegral (length (array (get "obligations" report)) - length unresolved)))
      "rule attempts counted as separate obligations"
    forM_ problems $ \problem -> do
      let matches = [o | o <- unresolved, get "symbol" o == get "symbol" problem, get "kind" o == get "kind" problem]
      case matches of
        [obligation] -> do
          check (get "code" problem == expectedCode kind && get "reasonCode" obligation == expectedCode kind)
            "narrow rule fallback hid the general rule category"
          check (get "source" problem == get "source" obligation
            && get "syntax" (get "source" problem) == toJSON [source]
            && get "module" (get "source" problem) == String "Public"
            && get "symbol" (get "source" problem) == get "symbol" problem)
            "classification lost source identity or location"
          check (get "models" problem == toJSON (["algebraic","also-affected"] :: [Text]))
            "classification lost affected model links"
          let attempts = array (get "causes" problem)
          check (map (get "rule") attempts == map String
            ["native.boolean-cases","native.finite-cases","native.algebraic-cases"])
            "failed rule alternatives were lost"
          check (get "code" (last attempts) == expectedCode kind
            && get "code" (attempts !! 1) == expectedCode D.Representation)
            "individual fallback categories were overwritten"
        _ -> fail "diagnostic does not identify exactly one unresolved obligation"
  -- The inventory sharing adapter remains textual outside translation, while
  -- its translation boundary is classified without changing the error API.
  case D.field inv "type" (object ["type" .= object ["$node" .= ("absent" :: Text)]]) of
    Left reason -> check (D.category reason == D.Syntax) "unreadable checked node misclassified"
    Right _ -> fail "unreadable checked node accepted"
  case P.readType inv [] (variable (-1) []) of
    Left reason -> check (D.category reason == D.Syntax) "specialization syntax category lost"
    Right _ -> fail "invalid specialization index accepted"
  case P.constrainLevel M.empty (P.LevelExpr 2 M.empty) 1 of
    Left reason -> check (D.category reason == D.Semantics) "specialization constraint category lost"
    Right _ -> fail "inconsistent level constraint accepted"
  forM_ [D.Syntax,D.Semantics,D.Representation] $ \kind -> do
    let reason = D.refusal kind "original"
        wrapped = D.context "callee: " reason
        combined = D.alternatives [("narrow",D.refusal D.Representation "not applicable")] ("general",wrapped)
    check (D.category combined == kind && D.message wrapped == "callee: original")
      "context or alternative aggregation reclassified the underlying failure"

-- Equal payload types and NoAbs still denote separate ordered helper inputs.
helperProvenanceChecks :: IO ()
helperProvenanceChecks = do
  let tailType = signature [named "Bool"] (named "Duo")
      helperType = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= named "Bool","info" .= info]
        ,"codomain" .= object ["binds" .= False,"body" .= tailType]]]
      def = declaration "duo" "constructor" helperType
      inv = Inventory Null (M.singleton "duo" def) M.empty M.empty
      sh = A.Shape "Duo" False [A.Constructor "duo"
        [("duo.payload0",A.Boolean),("duo.payload1",A.Boolean)] []] []
      shapes = M.singleton "Duo" sh
      helper inventory = case A.constructorCalculations inventory shapes of
        [c] -> c
        _ -> error "missing constructor helper"
      calc = helper inv
      doc = A.renderCalculationDoc inv shapes id calc
      trace = Trace.report inv inv doc
      checked = array (get "checkedOccurrences" trace)
      derivations = array (get "derivations" trace)
      inputIds = [get "derivation" t | t <- array (get "targetOccurrences" trace),get "role" t == String "input"]
      events = [get "evidence" d | d <- derivations,get "id" d `elem` inputIds]
      positions = map (get "position" . get "premises") events
      paths = [get "path" r | r <- checked,get "owner" r == String "duo",get "path" r /= toJSON ([] :: [Value])]
  check (Trace.validate (Trace.render doc) trace == Right ()) "constructor helper trace has unresolved domains"
  check (positions == [Number 0,Number 1]) "helper inputs lost their slot positions"
  check (all ((== Bool False) . get "binds" . get "premises") (take 1 events)) "NoAbs helper input was skipped"
  check (S.fromList paths == S.fromList [toJSON (["term","domain","type"] :: [Text])
    ,toJSON (["term","codomain","body","term","domain","type"] :: [Text])])
    "equal constructor domains were joined or given invented paths"
  forM_ [False,True] $ \a -> forM_ [False,True] $ \b -> check
    (eval [B a,B b] (A.body calc) == R "Duo" (M.fromList
      [("constructor",E "Duo.constructor-tag" "duo"),("duo.payload0",B a),("duo.payload1",B b)]))
    "helper input origins changed payload order or values"
  -- A stale/incomplete schema must not acquire guessed telescope locators.
  let broken = inv {declarations = M.singleton "duo" (set "type" (named "Duo") def)}
      brokenDoc = A.renderCalculationDoc broken shapes id (helper broken)
      brokenTrace = Trace.report broken broken brokenDoc
      missing = [get "evidence" d | d <- array (get "derivations" brokenTrace)
        ,get "rule" (get "evidence" d) `elem` [String "native.constructor-input",String "native.constructor-helper"]]
  check (Trace.render brokenDoc == Trace.render doc) "provenance fallback changed constructor helper bytes"
  check (not (null missing) && all ((/= Null) . get "unavailable") missing)
    "incomplete constructor schema was silently promoted"

-- Read the actual binding context: a NoAbs slot does not shift references,
-- while the same raw index after inserting Abs denotes a different input.
inputIndexProvenanceChecks :: IO ()
inputIndexProvenanceChecks = do
  let argInfo = object ["hiding" .= ("explicit" :: Text),"relevance" .= ("relevant" :: Text)
        ,"quantity" .= ("unrestricted" :: Text)]
      app value = object ["tag" .= ("apply" :: Text),"argument" .= object ["info" .= argInfo,"value" .= value]]
      indexed family value = object ["term" .= object ["tag" .= ("definition" :: Text)
        ,"symbol" .= (family :: Text),"eliminations" .= [app value]]]
      piType binds domain codomain = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= argInfo,"type" .= domain]
        ,"codomain" .= object ["binds" .= binds,"body" .= codomain]]]
      constructorType binds value = piType True (named "Bool")
        (piType binds (named "Bool") (piType True (indexed "Family" value) (named "Owner")))
      decl ty = declaration "make" "constructor" ty
      inventory ty = Inventory Null (M.singleton "make" (decl ty)) M.empty M.empty
      con = A.Constructor "make" [("make.payload0",A.Boolean),("make.payload1",A.Boolean)
        ,("make.payload2",A.Fibre "Family" [A.Input 0])] []
      ownerShape = A.Shape "Owner" False [con] []
      familyShape = A.Shape "Family" False [] [A.Boolean]
      shapes = M.fromList [("Owner",ownerShape),("Family",familyShape)]
      inv = inventory (constructorType False (variable 0 []))
      helper i ss = case A.constructorCalculations i ss of [c] -> c; _ -> error "helper"
      inspect i ss c = let doc = A.renderCalculationDoc i ss id c in (Trace.render doc,Trace.report i i doc)
      contracts report = [t | t <- array (get "targetOccurrences" report)
        ,get "role" t `elem` [String "index-contract",String "index-contract-boundary"]]
      roles i ss c = map (get "role") (contracts (snd (inspect i ss c)))
      original = helper inv shapes
      expectBoundary message i ss c = check (roles i ss c == [String "index-contract-boundary"]) message
      (model,trace) = inspect inv shapes original
  check (Trace.validate model trace == Right ()) "direct input-index trace does not resolve"
  check (roles inv shapes original == [String "index-contract"]) "NoAbs input index was not derived"
  let events = [get "evidence" d | d <- array (get "derivations" trace)
        ,get "rule" (get "evidence" d) == String "native.constructor-input-index"]
  check (map (get "bindingSlots" . get "premises") events == [toJSON ([0] :: [Int])])
    "input-index derivation lost the actual binder stack"
  let rebased = inventory (constructorType True (variable 1 []))
      captured = inventory (constructorType True (variable 0 []))
      projected = inventory (constructorType False (variable 0 ["field"]))
      computed = inventory (constructorType False (object ["tag" .= ("definition" :: Text)
        ,"symbol" .= ("compute" :: Text),"eliminations" .= [app (variable 0 [])]]))
  check (roles rebased shapes (helper rebased shapes) == [String "index-contract"]) "correctly rebased input index rejected"
  expectBoundary "captured equal-typed input was admitted" captured shapes (helper captured shapes)
  expectBoundary "projected input index escaped scope" projected shapes (helper projected shapes)
  expectBoundary "computed input index escaped scope" computed shapes (helper computed shapes)
  let noFamily = M.delete "Family" shapes
  expectBoundary "missing family layout was guessed" inv noFamily (helper inv noFamily)
  let functionInv = inv {declarations = M.adjust (set "kind" (String "function")) "make" (declarations inv)}
  expectBoundary "ordinary function index contract escaped scope" functionInv shapes original
  check (fst (inspect captured shapes (helper captured shapes)) == model) "refused provenance changed constraint bytes"
  -- Unsupported contracts occupy their original ordinal; later evidence must
  -- not slide onto them. The independently derived result keeps its ordinal.
  let mixedCon = A.Constructor "make" [("make.payload0",A.Boolean)
        ,("make.payload1",A.Fibre "Family" [A.Literal True])
        ,("make.payload2",A.Fibre "Family" [A.Input 0])] [A.Input 0]
      mixedShape = A.Shape "Owner" False [mixedCon] [A.Boolean]
      mixedShapes = M.insert "Owner" mixedShape shapes
      mixedType = piType True (named "Bool")
        (piType False (indexed "Family" (constructor "true" []))
          (piType False (indexed "Family" (variable 0 [])) (indexed "Owner" (variable 0 []))))
      mixedInv = inventory mixedType
      (mixedModel,mixedTrace) = inspect mixedInv mixedShapes (helper mixedInv mixedShapes)
  check (map (get "role") (contracts mixedTrace) == [String "index-contract-boundary",String "index-contract",String "index-contract"])
    "input/result contract evidence lost its original ordinal"
  check (Trace.validate mixedModel mixedTrace == Right ()) "mixed contract trace has unresolved origins"

  -- A single proper projection must retain both canonical field identity and
  -- the actual receiver slot, even when another equal-typed input is present.
  let projectedCon = A.Constructor "make" [("make.payload0",A.Named "Packet")
        ,("make.payload1",A.Named "Packet")
        ,("make.payload2",A.Fibre "Family" [A.Project (A.Input 0) "Packet.phase"])] []
      packetShape = A.Shape "Packet" True
        [A.Constructor "packet" [("Packet.phase",A.Named "Index"),("Packet.other",A.Named "Index")] []] []
      projectedShapes = M.fromList [("Owner",A.Shape "Owner" False [projectedCon] [])
        ,("Packet",packetShape),("Family",A.Shape "Family" False [] [A.Named "Index"])]
      projectionDecl name = set "projection" (object ["proper" .= ("Packet" :: Text),"index" .= (1 :: Int)])
        (declaration name "function" (piType False (named "Packet") (named "Index")))
      projectedType binds term = piType True (named "Packet")
        (piType binds (named "Packet") (piType False (indexed "Family" term) (named "Owner")))
      projectedInventory binds term = Inventory Null (M.fromList
        [("make",decl (projectedType binds term)),("Packet.phase",projectionDecl "Packet.phase")
        ,("Packet.other",projectionDecl "Packet.other")]) M.empty M.empty
      projectedInv = projectedInventory False (variable 0 ["Packet.phase"])
      projectedHelper i ss = case [c | c <- A.constructorCalculations i ss,A.calculationSymbol c == "make"] of
        [c] -> c; _ -> error "projected helper"
      projectedCalc = projectedHelper projectedInv projectedShapes
      (projectedModel,projectedTrace) = inspect projectedInv projectedShapes projectedCalc
      projectionEvents = [get "evidence" d | d <- array (get "derivations" projectedTrace)
        ,get "rule" (get "evidence" d) == String "native.constructor-projected-input-index"]
      refuseProjection message i ss c = do
        expectBoundary message i ss c
        check (fst (inspect i ss c) == projectedModel) "projection refusal changed generated bytes"
      modifyProjection f = projectedInv {declarations = M.adjust f "Packet.phase" (declarations projectedInv)}
      badMetadata key value = modifyProjection (set "projection" (set key value (get "projection" (projectionDecl "Packet.phase"))))
      badSignature ty = modifyProjection (set "type" ty)
  check (roles projectedInv projectedShapes projectedCalc == [String "index-contract"])
    "proper single-projection input contract was not derived"
  check (map (get "projection" . get "premises") projectionEvents == [String "Packet.phase"]
    && map (get "record" . get "premises") projectionEvents == [String "Packet"]
    && map (get "bindingSlots" . get "premises") projectionEvents == [toJSON ([0] :: [Int])])
    "projected contract lost canonical field, record, or receiver context"
  check (Trace.validate projectedModel projectedTrace == Right ()) "projected contract trace does not resolve"
  let rebound = projectedInventory True (variable 1 ["Packet.phase"])
  check (roles rebound projectedShapes (projectedHelper rebound projectedShapes) == [String "index-contract"])
    "projection receiver rebasing was rejected"
  mapM_ (\(message,i) -> refuseProjection message i projectedShapes (projectedHelper i projectedShapes))
    [("captured equal-typed receiver admitted",projectedInventory True (variable 0 ["Packet.phase"]))
    ,("equal-typed canonical field swap admitted",projectedInventory False (variable 0 ["Packet.other"]))
    ,("nested projection admitted",projectedInventory False (variable 0 ["Packet.phase","Packet.phase"]))
    ,("applied projection admitted",projectedInventory False
        (set "eliminations" (toJSON [object ["tag" .= ("project" :: Text),"symbol" .= ("Packet.phase" :: Text)]
          ,app (variable 0 [])]) (variable 0 [])))
    ,("missing proper projection metadata admitted",badMetadata "proper" Null)
    ,("wrong record owner admitted",badMetadata "proper" (String "OtherPacket"))
    ,("parameterized projection admitted",badMetadata "index" (Number 2))
    ,("non-function projection admitted",modifyProjection (set "kind" (String "constructor")))
    ,("wrong checked receiver type admitted",badSignature (piType False (named "OtherPacket") (named "Index")))
    ,("wrong checked result type admitted",badSignature (piType False (named "Packet") (named "OtherIndex")))
    ,("extra projection argument admitted",badSignature (piType True (named "Packet") (piType False (named "Packet") (named "Index"))))
    ,("hidden projection receiver admitted",badSignature (object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= set "hiding" (String "hidden") argInfo,"type" .= named "Packet"]
        ,"codomain" .= object ["binds" .= False,"body" .= named "Index"]]]))]
  let missingField = projectedInv {declarations = M.delete "Packet.phase" (declarations projectedInv)}
      noRecord = M.delete "Packet" projectedShapes
  refuseProjection "missing projection declaration guessed" missingField projectedShapes projectedCalc
  refuseProjection "unadmitted record field guessed" projectedInv noRecord projectedCalc

resultIndexProvenanceChecks :: IO ()
resultIndexProvenanceChecks = do
  let explicit = set "hiding" (String "explicit") info
      app v = set "argument" (object ["info" .= explicit,"value" .= v]) (application v)
      family values = object ["term" .= object ["tag" .= ("definition" :: Text)
        ,"symbol" .= ("Owner" :: Text),"eliminations" .= map app values]]
      piType binds codomain = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= explicit,"type" .= named "Bool"]
        ,"codomain" .= object ["binds" .= binds,"body" .= codomain]]]
      checked binds values = piType True (piType binds (family values))
      builtins = object ["builtins" .= object ["bool" .= ("Bool" :: Text)
        ,"true" .= ("true" :: Text),"false" .= ("false" :: Text)]]
      tone = set "constructors" (toJSON (["red","blue"] :: [Text]))
        (declaration "Tone" "datatype" (object ["term" .= object ["tag" .= ("sort" :: Text)]]))
      inventory binds values = Inventory builtins (M.fromList
        [("make",declaration "make" "constructor" (checked binds values)),("Tone",tone)
        ,("red",declaration "red" "constructor" (named "Tone"))
        ,("blue",declaration "blue" "constructor" (named "Tone"))]) M.empty M.empty
      shapes types expected = M.singleton "Owner" (A.Shape "Owner" False
        [A.Constructor "make" [("make.payload0",A.Boolean),("make.payload1",A.Boolean)] expected] types)
      helper i ss = case A.constructorCalculations i ss of [c] -> c; _ -> error "result helper"
      inspect i ss c = let doc = A.renderCalculationDoc i ss id c in (Trace.render doc,Trace.report i i doc)
      contracts trace = [t | t <- array (get "targetOccurrences" trace)
        ,get "role" t `elem` [String "index-contract",String "index-contract-boundary"]]
      roles i ss c = map (get "role") (contracts (snd (inspect i ss c)))
      ss = shapes [A.Boolean] [A.Input 0]
      inv = inventory False [variable 0 []]
      calc = helper inv ss
      (model,trace) = inspect inv ss calc
      events = [get "evidence" d | d <- array (get "derivations" trace)
        ,get "rule" (get "evidence" d) == String "native.constructor-result-index"]
      refuseUnchanged message i = do
        check (roles i ss (helper i ss) == [String "index-contract-boundary"]) message
        check (fst (inspect i ss (helper i ss)) == model) "result provenance refusal changed bytes"
  check (roles inv ss calc == [String "index-contract"]) "NoAbs constructor result was not derived"
  check (map (get "bindingSlots" . get "premises") events == [toJSON ([0] :: [Int])]
    && map (get "expectedInput" . get "premises") events == [Number 0]) "result contract lost actual input identity"
  check (Trace.validate model trace == Right ()) "result trace has unresolved references"
  let rebased = inventory True [variable 1 []]
  check (roles rebased ss (helper rebased ss) == [String "index-contract"]) "result receiver rebasing failed"
  refuseUnchanged "result captured an equal-typed input" (inventory True [variable 0 []])
  refuseUnchanged "projected result index escaped scope" (inventory False [variable 0 ["field"]])
  refuseUnchanged "negative result index admitted" (inventory False [variable (-1) []])
  refuseUnchanged "wrong result arity admitted" (inventory False [variable 0 [],variable 0 []])
  let ordinary = inv {declarations = M.adjust (set "kind" (String "function")) "make" (declarations inv)}
  check (roles ordinary ss calc == [String "index-contract-boundary"]) "ordinary function result admitted"
  check (roles inv ss (calc {A.body = A.Input 0}) == [String "index-contract-boundary"])
    "result evidence admitted an unrelated calculation body"
  forM_ [False,True] $ \b -> do
    let constShapes = shapes [A.Boolean] [A.Literal b]
        constInv value = inventory False [constructor value []]
        valid = constInv (if b then "true" else "false")
        wrong = constInv (if b then "false" else "true")
    check (roles valid constShapes (helper valid constShapes) == [String "index-contract"])
      "Boolean result constant was not derived"
    check (roles wrong constShapes (helper wrong constShapes) == [String "index-contract-boundary"])
      "Boolean result constant changed value"
  let enumShapes = shapes [A.Named "Tone"] [A.Enumeration "Tone" "red"]
      enumInv = inventory False [constructor "red" []]
      wrongEnum = inventory False [constructor "blue" []]
      brokenEnum = enumInv {declarations = M.adjust (set "type" (signature [named "Bool"] (named "Tone"))) "red" (declarations enumInv)}
  check (roles enumInv enumShapes (helper enumInv enumShapes) == [String "index-contract"])
    "finite enum result constant was not derived"
  check (roles wrongEnum enumShapes (helper wrongEnum enumShapes) == [String "index-contract-boundary"])
    "different constructor of the same finite domain was admitted"
  check (roles brokenEnum enumShapes (helper brokenEnum enumShapes) == [String "index-contract-boundary"])
    "non-finite constructor payload was admitted as a result constant"
  let mixedShapes = shapes [A.Boolean,A.Boolean,A.Named "Tone"]
        [A.Input 0,A.Project (A.Input 0) "field",A.Enumeration "Tone" "red"]
      mixedInv = inventory False [variable 0 [],variable 0 ["field"],constructor "red" []]
      (mixedModel,mixedTrace) = inspect mixedInv mixedShapes (helper mixedInv mixedShapes)
      mixedTargets = contracts mixedTrace
  check (map (get "role") mixedTargets == [String "index-contract",String "index-contract-boundary",String "index-contract"])
    "unsupported result index displaced later evidence"
  check (Trace.validate mixedModel mixedTrace == Right ()) "mixed result trace references do not resolve"

naturalChecks :: IO ()
naturalChecks = do
  let universe = universeAt (level 0)
      nat = set "constructors" (toJSON (["zero","suc"] :: [Text])) (declaration "Nat" "datatype" universe)
      zeroDef = set "family" (String "Nat") (declaration "zero" "constructor" (named "Nat"))
      sucDef = set "family" (String "Nat") (declaration "suc" "constructor" (signature [named "Nat"] (named "Nat")))
      primitive s p out = set "primitive" (String p) (declaration s "primitive" (signature [named "Nat",named "Nat"] (named out)))
      primitiveDefs = [primitive "add" "PrimNatPlus" "Nat",primitive "monus" "PrimNatMinus" "Nat"
        ,primitive "multiply" "PrimNatTimes" "Nat",primitive "less" "PrimNatLess" "Bool",primitive "equal" "PrimNatEquality" "Bool"]
      literal n = object ["tag" .= ("literal" :: Text),"literal" .= object ["tag" .= ("natural" :: Text),"value" .= (n :: Integer)]]
      predecessor = operation "predecessor" ["Nat"] "Nat" (split 0 [("zero",0,done 0 (literal 0)),("suc",1,done 1 (variable 0 []))])
      defs = [nat,zeroDef,sucDef,predecessor] ++ primitiveDefs
      inv = Inventory (object ["builtins" .= object ["nat" .= ("Nat" :: Text),"zero" .= ("zero" :: Text),"suc" .= ("suc" :: Text),"bool" .= ("Bool" :: Text)]])
        (M.fromList [(string (get "name" d),d) | d <- defs]) M.empty
        (M.singleton "numbers" (S.fromList [(string (get "name" d),if get "kind" d `elem` [String "function",String "primitive"] then "behavior" else "structure") | d <- defs]))
      calculations = A.functions inv M.empty M.empty
  table <- traverse (either (fail . show) pure) calculations
  sequenceChecks inv
  forM_ [0,1,7,10^(100 :: Int)] $ \a -> do
    check (evalWith table [Z a] (A.body (table M.! "predecessor")) == Z (max 0 (a-1))) "natural branch lost predecessor"
    forM_ [0,2,11,10^(101 :: Int)] $ \b ->
      forM_ [("add",Z (a+b)),("monus",Z (max 0 (a-b))),("multiply",Z (a*b)),("less",B (a<b)),("equal",B (a==b))] $ \(name,expected) ->
        check (evalWith table [Z a,Z b] (A.body (table M.! name)) == expected) "native arithmetic changed unbounded natural semantics"
  check (length (A.calculationContracts id (table M.! "add")) == 3) "natural boundary omitted finiteness"
  let indexContext = reverse [Just (P.Runtime (P.Named "Nat" []) (P.IndexInput i)) | i <- [0,1]]
  forM_ ["add","sumNatural"] $ \symbol -> do
    let indexed = inv {declarations = M.insert symbol (primitive symbol "PrimNatPlus" "Nat") (declarations inv)}
        addition = call symbol [variable 1 [],variable 0 []] []
    check (P.readType indexed indexContext addition == Right
      (P.Runtime (P.Named "Nat" []) (P.IndexCall symbol [] [P.IndexInput 0,P.IndexInput 1])))
      "primitive addition in a dependent index was mistaken for a named carrier"
    forM_ [[variable 0 []],[variable 1 [],variable 0 [],literal 0],[literal (-1),variable 0 []]] $ \arguments ->
      check (isLeft (P.readType indexed indexContext (call symbol arguments [])))
        "primitive index admitted an incomplete, excess, or invalid argument"
  let malformed = primitive "bad" "PrimNatPlus" "Bool"
      missing = set "primitive" Null (primitive "bad" "PrimNatPlus" "Nat")
      negative = operation "negative" [] "Nat" (done 0 (literal (-1)))
  forM_ [malformed,missing,negative] $ \d ->
    check (isLeft (A.function inv M.empty M.empty d)) "invalid numeric schema admitted"
  let v i = variable i []
      plus a b = call "add" [a,b] []
      successor x = constructor "suc" [x]
      indexed x = object ["term" .= call "Measured" [x] []]
      measured = set "constructors" (toJSON (["measured"] :: [Text])) $
        declaration "Measured" "datatype" (signature [named "Nat"] universe)
      measuredCtor = set "family" (String "Measured") $
        declaration "measured" "constructor" (signature [named "Nat"] (indexed (v 0)))
      nested = set "sourceSyntax" (toJSON [object []]) $
        set "compiled" (done 2 (constructor "measured" [successor (plus (v 1) (v 0))])) $
        declaration "nestedAddition" "function"
          (signature [named "Nat",named "Nat"] (indexed (plus (successor (v 1)) (v 0))))
      branching = set "sourceSyntax" (toJSON [object []]) $
        set "compiled" (split 0 [("zero",0,done 1 (constructor "measured" [v 0]))
          ,("suc",1,done 2 (constructor "measured" [successor (plus (v 1) (v 0))]))]) $
        declaration "branchAddition" "function"
          (signature [named "Nat",named "Nat"] (indexed (plus (v 1) (v 0))))
      additions = [measured,measuredCtor,nested,branching]
      indexedInv = inv {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations inv)
        ,modelRequirements = M.insert "arithmetic-indices" (S.fromList
          [("Measured","structure"),("measured","structure"),("nestedAddition","behavior"),("branchAddition","behavior")]) (modelRequirements inv)}
      (shapes,errors) = A.discover indexedInv M.empty
  check (M.null errors) (show errors)
  nestedTable <- traverse (either (fail . show) pure) (A.functions indexedInv M.empty shapes)
  forM_ [(0,0),(4,7),(10^(100 :: Int),10^(101 :: Int))] $ \(a,b) -> do
    let result = R "Measured" (M.fromList [("constructor",E "Measured.constructor-tag" "measured")
          ,("Measured.index0",Z (a+b+1)),("measured.payload0",Z (a+b+1))])
    check (evalWith nestedTable [Z a,Z b] (A.body (nestedTable M.! "nestedAddition")) == result)
      "addition under a successor lost its complete indexed result"
    let branchResult = R "Measured" (M.fromList [("constructor",E "Measured.constructor-tag" "measured")
          ,("Measured.index0",Z (a+b)),("measured.payload0",Z (a+b))])
    check (evalWith nestedTable [Z a,Z b] (A.body (nestedTable M.! "branchAddition")) == branchResult)
      "natural branch refinement failed to preserve its arithmetic index"
  let wrong = indexedInv {declarations = M.adjust
        (set "compiled" (done 2 (constructor "measured" [successor (successor (plus (v 1) (v 0)))])))
        "nestedAddition" (declarations indexedInv)}
  check (isLeft (A.functions wrong M.empty shapes M.! "nestedAddition"))
    "different arithmetic result indices were treated as equal"
  let noBranch = indexedInv {declarations = M.adjust (set "compiled" (done 2
        (constructor "measured" [successor (plus (call "monus" [v 1,literal 1] []) (v 0))])))
        "branchAddition" (declarations indexedInv)}
  check (isLeft (A.functions noBranch M.empty shapes M.! "branchAddition"))
    "predecessor/successor equality escaped its positive natural branch"

constructorFibreChecks :: IO ()
constructorFibreChecks = do
  let piType binds domain codomain = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= info,"type" .= domain]
        ,"codomain" .= object ["binds" .= binds,"body" .= codomain]]]
      proof value = object ["term" .= call "Proof" [value] []]
      absurd n = object ["tag" .= ("absurd" :: Text),"binders" .= replicate n Null]
      token c fields = A.Construct "Token" (("constructor",A.Enumeration "Token.constructor-tag" c):fields)
      witness = A.Constructor "witness" [("witness.payload0",A.Boolean)]
        [token "packed" [("packed.payload0",A.Input 0)]]
      tokenShape = A.Shape "Token" False [A.Constructor "packed" [("packed.payload0",A.Boolean)] [],A.Constructor "empty" [] []] []
      proofShape = A.Shape "Proof" False [witness] [A.Named "Token"]
      shapes = M.fromList [("Token",tokenShape),("Proof",proofShape)]
      inv = Inventory (object ["builtins" .= object ["bool" .= ("Bool" :: Text)]]) M.empty M.empty M.empty
      decoder = set "type" (piType True (named "Token") (piType False (proof (variable 0 [])) (named "Bool")))
        $ operation "unpack" [] "Bool" (split 0
          [("packed",1,done 2 (variable 1 [])),("empty",0,absurd 1)])
  calc <- either (fail . show) pure (A.function inv M.empty shapes decoder)
  let lazyToken = set "lazy" (Bool True) (split 0 [("packed",1,done 2 (variable 1 []))])
      witnessed = set "compiled" (split 1 [("witness",1,lazyToken)]) decoder
  witnessedCalc <- either (fail . show) pure (A.function inv M.empty shapes witnessed)
  let pairedWitness = set "type" (piType True (named "Token")
        (piType False (proof (variable 0 []))
          (piType False (proof (variable 0 [])) (proof (variable 0 [])))))
        $ set "compiled" (split 1 [("witness",1,split 2
            [("witness",1,done 3 (constructor "witness" [variable 0 []]))])]) decoder
  pairedCalc <- either (fail . show) pure (A.function inv M.empty shapes pairedWitness)
  forM_ [False,True] $ \b -> do
    let value = R "Token" (M.fromList [("constructor",E "Token.constructor-tag" "packed"),("packed.payload0",B b)])
    check (eval [value,N] (A.body calc) == B b) "constructor-index refinement changed a valid payload"
    let proofValue = R "Proof" (M.fromList [("constructor",E "Proof.constructor-tag" "witness")
          ,("Proof.index0",value),("witness.payload0",B b)])
    check (eval [value,proofValue] (A.body witnessedCalc) == B b)
      "lazy match ignored the constructor established by a dependent witness"
    check (eval [value,proofValue,proofValue] (A.body pairedCalc) == proofValue)
      "equal constructor indices did not equate corresponding witness payloads"
  check (isLeft (A.function inv M.empty shapes (set "compiled" lazyToken decoder)))
    "lazy match guessed a constructor without a preceding witness split"
  let unrelatedLazy = set "type" (piType False (named "Token")
        (piType True (named "Token") (piType False (proof (variable 0 [])) (named "Bool"))))
        $ set "compiled" (split 2 [("witness",1,set "lazy" (Bool True)
            (split 0 [("packed",1,done 3 (variable 2 []))]))]) decoder
  check (isLeft (A.function inv M.empty shapes unrelatedLazy))
    "a dependent witness refined an unrelated token input"
  let inhabited = proofShape {A.variants = [witness,A.Constructor "emptyWitness" [] [token "empty" []]]}
  check (isLeft (A.function inv M.empty (M.insert "Proof" inhabited shapes) decoder))
    "absurd branch admitted despite an inhabitant at the selected constructor"
  let missingPayload = set "compiled" (split 0 [("packed",1,absurd 2),("empty",0,absurd 1)]) decoder
  check (isLeft (A.function inv M.empty shapes missingPayload))
    "unknown payload was treated as evidence of an empty fibre"
  let unrelated = set "type" (piType False (named "Token")
        (piType True (named "Token") (piType False (proof (variable 0 [])) (named "Bool"))))
        $ set "compiled" (split 0 [("packed",1,done 3 (variable 2 [])),("empty",0,absurd 2)]) decoder
  check (isLeft (A.function inv M.empty shapes unrelated))
    "constructor choice for another input justified an absurd branch"
  let indexedToken c fields = A.Construct "IndexedToken"
        (("constructor",A.Enumeration "IndexedToken.constructor-tag" c):("IndexedToken.index0",A.Input 0):fields)
      indexedShape = A.Shape "IndexedToken" False
        [A.Constructor "indexedPacked" [("indexedPacked.payload0",A.Boolean),("indexedPacked.payload1",A.Boolean)] [A.Input 0]
        ,A.Constructor "indexedEmpty" [("indexedEmpty.payload0",A.Boolean)] [A.Input 0]] [A.Boolean]
      indexedProof = A.Shape "IndexedProof" False
        [A.Constructor "indexedWitness" [("indexedWitness.payload0",A.Boolean),("indexedWitness.payload1",A.Boolean)]
          [A.Input 0,indexedToken "indexedPacked" [("indexedPacked.payload0",A.Input 0),("indexedPacked.payload1",A.Input 1)] ]]
        [A.Boolean,A.Fibre "IndexedToken" [A.Input 0]]
      indexedShapes = M.fromList [("IndexedToken",indexedShape),("IndexedProof",indexedProof)]
      tokenType b = object ["term" .= call "IndexedToken" [b] []]
      proofType b t = object ["term" .= call "IndexedProof" [b,t] []]
      indexedDecoder = set "type" (piType True (named "Bool") (piType True (tokenType (variable 0 []))
        (piType False (proofType (variable 1 []) (variable 0 [])) (named "Bool"))))
        $ operation "indexedUnpack" [] "Bool" (split 1
          [("indexedPacked",2,done 4 (variable 1 [])),("indexedEmpty",1,absurd 3)])
  _ <- either (fail . show) pure (A.function inv M.empty indexedShapes indexedDecoder)
  let indexedInhabited = indexedProof {A.variants = A.variants indexedProof ++
        [A.Constructor "indexedEmptyWitness" [("indexedEmptyWitness.payload0",A.Boolean)]
          [A.Input 0,indexedToken "indexedEmpty" [("indexedEmpty.payload0",A.Input 0)]] ]}
  check (isLeft (A.function inv M.empty (M.insert "IndexedProof" indexedInhabited indexedShapes) indexedDecoder))
    "indexed constructor tag separation ignored an inhabitant of the empty branch"

constructorScopeChecks :: IO ()
constructorScopeChecks = do
  let universe = universeAt (level 0)
      arrow binds domain codomain = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= info,"type" .= domain]
        ,"codomain" .= object ["binds" .= binds,"body" .= codomain]]]
      applied name args = object ["term" .= call name args []]
      var i = object ["term" .= variable i []]
      bool = P.Named "Bool" []
      boolean = set "constructors" (toJSON (["true","false"] :: [Text])) $ declaration "Bool" "datatype" universe
      booleanConstructor c = set "family" (String "Bool") $ declaration c "constructor" (named "Bool")
      wrapped value = applied "Wrapped" [value]
      wrapper = set "parameters" (Number 1) $ declaration "Wrapped" "datatype" (arrow False (named "Bool") universe)
      mark = set "parameters" (Number 1) $ set "family" (String "Wrapped") $ declaration "mark" "constructor"
        (arrow True (named "Bool") (arrow True (named "Bool") (wrapped (variable 1 []))))
      indexed = declaration "Indexed" "datatype" (arrow True (named "Bool")
        (arrow False (wrapped (variable 0 [])) universe))
      packed = set "parameters" (Number 1) $ declaration "Packed" "record" (arrow False (named "Bool") universe)
      projection = set "projection" (object ["proper" .= ("Packed" :: Text),"index" .= (2 :: Int)])
        $ declaration "value" "function" (arrow True (named "Bool")
          (arrow True (applied "Packed" [variable 0 []]) (wrapped (variable 1 []))))
      holder = set "parameters" (Number 1) $ declaration "Holder" "datatype" (arrow True universe universe)
      hold = set "parameters" (Number 1) $ set "family" (String "Holder") $ declaration "hold" "constructor"
        (arrow True universe (arrow False (var 0) (applied "Holder" [variable 0 []])))
      holding = set "parameters" (Number 1) $ declaration "Holding" "datatype" (arrow True universe
        (arrow False (applied "Holder" [variable 0 []]) universe))
      defs = [boolean,booleanConstructor "true",booleanConstructor "false",wrapper,mark,indexed,packed,projection,holder,hold,holding]
      inv = Inventory (object ["builtins" .= object ["bool" .= ("Bool" :: Text)]])
        (M.fromList [(string (get "name" d),d) | d <- defs]) M.empty M.empty
      yes = P.IndexConstructor "true" [] []
      no = P.IndexConstructor "false" [] []
      member = P.Named "Wrapped" [P.Runtime bool yes]
      term = call "Indexed" [constructor "true" [],constructor "mark" [constructor "false" []]] []
  check (P.readType inv [] term == Right (P.Named "Indexed"
    [P.Runtime bool yes,P.Runtime member (P.IndexConstructor "mark" [] [no])]))
    "omitted runtime constructor parameter was not recovered from the preceding family index"
  check (isLeft (P.readType inv [] (call "Indexed" [constructor "true" [],constructor "mark" []] [])))
    "omitted value parameter recovery admitted a missing constructor payload"
  check (P.readType inv [Just (P.Runtime (P.Named "Packed" [P.Runtime bool yes]) (P.IndexInput 7))]
    (variable 0 ["value"]) == Right (P.Runtime member (P.IndexProject "value" [] (P.IndexInput 7))))
    "record projection lost its runtime parameter or actual receiver"
  let contextual = P.Named "Wrapped" [P.Runtime bool (P.IndexInput 0)]
      holderTerm = call "Holding" [variable 1 [],constructor "hold" [variable 0 []]] []
      expected = P.Named "Holding" [contextual,P.Runtime (P.Named "Holder" [contextual])
        (P.IndexConstructor "hold" [contextual] [P.IndexInput 5])]
  check (P.readType inv [Just (P.Runtime contextual (P.IndexInput 5)),Just contextual] holderTerm == Right expected)
    "constructor substitution captured an index belonging to its caller's static argument"
  check (isLeft (P.readType inv [Just (P.Runtime (P.Named "Wrapped" [P.Runtime bool (P.IndexInput 1)]) (P.IndexInput 5)),Just contextual] holderTerm))
    "constructor substitution admitted a payload at a different caller index"

familyParameterChecks :: IO ()
familyParameterChecks = do
  let universe = universeAt (level 0)
      arrow binds domain codomain = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["info" .= info,"type" .= domain]
        ,"codomain" .= object ["binds" .= binds,"body" .= codomain]]]
      variableType index args = object ["term" .= object ["tag" .= ("variable" :: Text),"index" .= (index :: Int)
        ,"eliminations" .= map application args]]
      familyDomain = arrow False (named "Bool") universe
      resultType = variableType 1 [get "term" (variableType 0 [])]
      declaration' = set "projection" Null $ declaration "selectFamily" "function"
        (arrow True familyDomain (arrow True (named "Bool") resultType))
      inv = Inventory (object []) M.empty M.empty M.empty
      bool = P.Named "Bool" []
      schema = P.FamilyParameter 0 [bool] (P.LevelExpr 0 M.empty)
      family = P.OpenFamily 0 [bool] (P.LevelExpr 0 M.empty)
      value = P.Runtime bool (P.IndexInput 0)
      applicationTerm = get "term" resultType
  sig <- either (fail . show) pure (P.signature inv declaration')
  check (P.parameters sig == 1 && P.inputs sig == [bool]
    && P.parameterKinds sig == [P.FamilyKind [bool] (P.LevelExpr 0 M.empty)]
    && P.output sig == P.FamilyApplication schema [value]) "checked family telescope/application lost binder or index"
  resolved <- either (fail . show) pure (P.substitute [family] (P.output sig))
  check (resolved == P.FamilyApplication family [value]) "family substitution discarded runtime index"
  check (P.readType inv [Just value,Just schema] applicationTerm == Right (P.FamilyApplication schema [value]))
    "family application did not retain checked index domain"
  let wrong = P.Runtime (P.Named "Other" []) (P.IndexInput 0)
  check (isLeft (P.readType inv [Just wrong,Just schema] applicationTerm)) "incompatible family index domain admitted"
  check (isLeft (P.readType inv [Just value,Just schema] (get "term" (variableType 1 [get "term" (variableType 0 []),get "term" (variableType 0 [])]))))
    "overapplied family parameter admitted"
  let dependent = arrow True (named "Bool") (arrow False (variableType 0 []) universe)
      unsupported = set "type" (arrow True dependent (named "Bool")) declaration'
  check (isLeft (P.signature inv unsupported)) "dependent family argument domain silently flattened"
  -- An index constructor omits its family argument. Recover that argument
  -- while reading a symbolic signature, before open-root instantiation.
  let wrapper familyArg = object ["term" .= call "FamilyWrapper" [get "term" familyArg] []]
      wrapperType = set "parameters" (Number 1) $ declaration "FamilyWrapper" "datatype"
        (arrow True familyDomain universe)
      wrapperConstructor = set "family" (String "FamilyWrapper") $ declaration "familyWrap" "constructor"
        (arrow True familyDomain (wrapper (variableType 0 [])))
      indexedType = set "parameters" (Number 1) $ declaration "FamilyIndexed" "datatype"
        (arrow True familyDomain (arrow False (wrapper (variableType 0 [])) universe))
      symbolicInv = inv {declarations = M.fromList
        [("FamilyWrapper",wrapperType),("familyWrap",wrapperConstructor),("FamilyIndexed",indexedType)]}
      indexedTerm = call "FamilyIndexed" [get "term" (variableType 0 []),constructor "familyWrap" []] []
      expectedIndex = P.Runtime (P.Named "FamilyWrapper" [schema]) (P.IndexConstructor "familyWrap" [schema] [])
  check (P.readType symbolicInv [Just schema] indexedTerm == Right (P.Named "FamilyIndexed" [schema,expectedIndex]))
    "symbolic family equality did not recover the omitted index-constructor argument"
  forM_ [P.FamilyParameter 0 [P.Named "Other" []] (P.LevelExpr 0 M.empty),
         P.FamilyParameter 0 [bool] (P.LevelExpr 1 M.empty)] $ \incompatible ->
    check (isLeft (P.readType symbolicInv [Just incompatible] indexedTerm))
      "symbolic family inference merged incompatible domains or universes"
  let payload f w = object ["term" .= call "FamilyPayload" [get "term" f,get "term" w] []]
      payloadType = set "parameters" (Number 1) $ declaration "FamilyPayload" "datatype"
        (arrow True familyDomain (arrow False (wrapper (variableType 0 [])) universe))
      payloadConstructor = set "family" (String "FamilyPayload") $ declaration "familyPayload" "constructor"
        (arrow True familyDomain (arrow True (wrapper (variableType 0 []))
          (payload (variableType 1 []) (variableType 0 []))))
      dependentType = set "parameters" (Number 1) $ declaration "DependentIndices" "datatype"
        (arrow True familyDomain (arrow True (wrapper (variableType 0 []))
          (arrow False (payload (variableType 1 []) (variableType 0 [])) universe)))
      otherConstructor = set "name" (String "otherWrap") wrapperConstructor
      dependentInv = symbolicInv {declarations = M.union (declarations symbolicInv) (M.fromList
        [("FamilyPayload",payloadType),("familyPayload",payloadConstructor),
         ("DependentIndices",dependentType),("otherWrap",otherConstructor)])}
      dependentTerm second = call "DependentIndices"
        [get "term" (variableType 0 []),constructor "familyWrap" [],
         constructor "familyPayload" [constructor second []]] []
      member = P.Runtime (P.Named "FamilyPayload" [schema,expectedIndex])
        (P.IndexConstructor "familyPayload" [schema] [P.IndexConstructor "familyWrap" [schema] []])
  check (P.readType dependentInv [Just schema] (dependentTerm "familyWrap")
      == Right (P.Named "DependentIndices" [schema,expectedIndex,member]))
    "later index domain did not retain the preceding constructor value"
  check (isLeft (P.readType dependentInv [Just schema] (dependentTerm "otherWrap")))
    "dependent index admitted a member at a different preceding value"
  let pairType = set "parameters" (Number 2) $ declaration "DependentPair" "record"
        (arrow True universe (arrow True (arrow False (variableType 0 []) universe) universe))
      pairInv = inv {declarations = M.singleton "DependentPair" pairType}
      lambda slot = object ["tag" .= ("lambda" :: Text),"abstraction" .= object ["binds" .= True
        ,"body" .= get "term" (variableType 1 [get "term" (variableType slot [])])]]
      pairTerm body = get "term" (set "term" (call "DependentPair" [get "term" (named "Bool"),body] []) (object []))
      contextual = P.Runtime bool (P.IndexInput 0)
  parsed <- either (fail . show) pure (P.readType pairInv [Just family] (pairTerm (lambda 0)))
  case parsed of
    P.Named "DependentPair" [_,closure] -> do
      resolved <- either (fail . show) pure (P.substitute [closure]
        (P.FamilyApplication (P.FamilyParameter 0 [bool] (P.LevelExpr 0 M.empty)) [contextual]))
      check (resolved == P.FamilyApplication family [contextual]) "first-order family beta substitution lost its member index"
    _ -> fail "type-family lambda did not retain its domain and member"
  check (isLeft (P.readType pairInv [Just family] (pairTerm (lambda 1))))
    "type-family binder confused its own argument with the preceding family parameter"
  let closure slot = P.FamilyExpression bool slot
        (P.FamilyApplication family [P.Runtime bool (P.IndexLocal slot)]) (P.LevelExpr 0 M.empty)
  check (P.typeKey (closure 0) == P.typeKey (closure 7)) "alpha-renaming a family binder changed its instance identity"
  check (P.typeKey (closure 0) /= P.typeKey (P.FamilyExpression bool 0
    (P.FamilyApplication (P.OpenFamily 1 [bool] (P.LevelExpr 0 M.empty)) [P.Runtime bool (P.IndexLocal 0)]) (P.LevelExpr 0 M.empty)))
    "distinct family bindings were merged"
  let callback = P.Callable [bool] bool
      contextualFamily input slot = P.FamilyExpression bool slot
        (P.FamilyApplication family [P.Runtime bool (P.IndexApply (P.IndexTyped callback input) (P.IndexLocal slot))])
        (P.LevelExpr 0 M.empty)
      carrier input slot = P.Named "DependentPair" [bool,contextualFamily input slot]
  check (P.typeKey (carrier (P.IndexInput 0) 0) == P.typeKey (carrier (P.IndexInput 7) 3))
    "a free callback under a family binder leaked its caller position into the carrier identity"
  check (P.typeKey (carrier (P.IndexInput 0) 0) /= P.typeKey (P.Named "DependentPair" [bool,closure 0]))
    "a computed family refinement was merged with a direct family selection"

reductionChecks :: IO ()
reductionChecks = do
  let lambda binds body = object ["tag" .= ("lambda" :: Text),"abstraction" .= object ["binds" .= binds,"body" .= body]]
      local = Reduction.variable
      safe d = set "opaque" (Bool False) $ set "terminates" (Bool True) $ set "sourceModule" (String "Checked") d
      wrap = safe (operation "wrap" ["Bool"] "Bool" (done 1 (local 0)))
      short = safe (operation "short" ["Bool"] "Bool" (done 0 (call "wrap" [] [])))
      bottom = call "unrepresentedProof" [] []
      box = set "fields" (toJSON (["value","evidence"] :: [Text])) $ set "constructor" (String "box") $ declaration "Box" "record" (universeAt (level 0))
      ctor = set "family" (String "Box") (declaration "box" "constructor" (signature [named "Bool",named "Proof"] (named "Box")))
      make = safe (operation "make" ["Bool"] "Box" (done 1 (constructor "box" [local 0,bottom])))
      doc = object ["checking" .= [object ["module" .= ("Checked" :: Text),"safe" .= True,"terminationCheck" .= True]]]
      inv = Inventory doc (M.fromList [(string (get "name" d),d) | d <- [wrap,short,box,ctor,make]]) M.empty M.empty
      reduce t = fst <$> Reduction.reduceHead inv t
  check (Reduction.substituteTerms [local 0] (lambda True (local 1)) == Just (lambda True (local 1))) "substitution captured an outer variable"
  check (Reduction.substituteTerms [local 2] (lambda True (local 0)) == Just (lambda True (local 0))) "substitution replaced a bound variable"
  check (Reduction.substituteTerms [local 2] (lambda False (local 0)) == Just (lambda False (local 2))) "NoAbs was incorrectly treated as a binder"
  check (Reduction.applyTerms (lambda True (local 0)) [constructor "true" []] == Just (constructor "true" [])) "beta reduction failed"
  check (reduce (call "short" [local 0] []) == Just (local 0)) "eta-short checked wrapper did not reduce"
  check (reduce (call "make" [local 0] ["value"]) == Just (local 0)) "projection evaluated or retained an unused field"
  check (reduce (call "make" [local 0] ["evidence"]) /= Just (local 0)) "proof field was identified with the computational field"
  let copied = set "moduleInstanceCopy" (Bool True) $ set "canonicalConstructor" (String "box")
        $ set "name" (String "copiedBox") ctor
      aliases = inv {declarations = M.insert "copiedBox" copied (declarations inv)}
      aliased = constructor "copiedBox" [local 0,bottom]
  check ((fst <$> Reduction.reduceHead aliases aliased) == Just (constructor "box" [local 0,bottom]))
    "canonical constructor identity did not preserve the exact payload spine"
  forM_ [set "moduleInstanceCopy" (Bool False),set "abstract" (Bool True),set "canonicalConstructor" Null] $ \change ->
    check (Reduction.reduceHead (aliases {declarations = M.adjust change "copiedBox" (declarations aliases)}) aliased == Nothing)
      "constructor alias reduced without checked identity evidence"
  let untrusted = inv {document = Null}
  check (Reduction.reduceHead untrusted (call "wrap" [local 0] []) == Nothing) "unchecked termination flag justified unfolding"
  let opaque = inv {declarations = M.adjust (set "opaque" (Bool True)) "wrap" (declarations inv)}
  check (Reduction.reduceHead opaque (call "wrap" [local 0] []) == Nothing) "opaque definition was unfolded"

closureChecks :: Inventory -> IO ()
closureChecks base = do
  let piType binds a b = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= a,"info" .= info]
        ,"codomain" .= object ["binds" .= binds,"body" .= b]]]
      varType i = object ["term" .= variable i []]
      fn a b = piType False a b
      safe d = set "opaque" (Bool False) $ set "terminates" (Bool True) $ set "sourceModule" (String "Checked") d
      invoke term args = set "eliminations" (toJSON (array (get "eliminations" term) ++ map application args)) term
      applyOnce = safe $ set "type" (piType True (universeAt (level 0)) (fn (fn (varType 0) (varType 0)) (fn (varType 0) (varType 0))))
        $ operation "applyOnce" [] "Bool" (done 3 (invoke (variable 1 []) [variable 0 []]))
      xor = safe $ operation "xor" ["Bool","Bool"] "Bool" $ split 0
        [("false",0,done 1 (variable 0 [])),("true",0,split 0
          [("false",0,done 0 (constructor "true" [])),("true",0,done 0 (constructor "false" []))])]
      caller = safe $ operation "closureCaller" ["Bool","Bool"] "Bool" $ done 2
        (call "applyOnce" [get "term" (named "Bool"),call "xor" [variable 1 []] [],variable 0 []] [])
      lambda = object ["tag" .= ("lambda" :: Text),"abstraction" .= object ["binds" .= True
        ,"body" .= call "xor" [variable 2 [],variable 0 []] []]]
      lambdaCaller = safe $ operation "lambdaCaller" ["Bool","Bool"] "Bool" $ done 2
        (call "applyOnce" [get "term" (named "Bool"),lambda,variable 0 []] [])
      bodyOnlyType = safe $ set "type" (piType True (universeAt (level 0))
        (fn (named "Callbacks") (universeAt (level 0))))
        $ operation "bodyOnlyType" [] "Bool"
          (set "eta" (object ["constructor" .= ("callbacks" :: Text),"fields" .= (["callback"] :: [Text])
            ,"branch" .= object ["arity" .= (1 :: Int),"tree" .= done 2
              (call "chooseSchema" [variable 1 [],invoke (variable 0 []) [constructor "true" []]] [])]]) (split 1 []))
      chooseSchema = safe $ set "type" (piType True (universeAt (level 0)) (fn (named "Bool") (universeAt (level 0))))
        $ operation "chooseSchema" [] "Bool" (split 1
          [("true",0,done 1 (call "BodyPayload" [variable 0 []] []))
          ,("false",0,done 1 (call "BodyPayload" [get "term" (named "Bool")] []))])
      bodyOnlyCaller = safe $ set "type" (piType True (universeAt (level 0)) (fn (named "Bool") (universeAt (level 0))))
        $ operation "bodyOnlyCaller" [] "Bool" (done 2
          (call "bodyOnlyType" [variable 1 [],constructor "callbacks" [call "xor" [variable 0 []] []]] []))
      bodyPayload = set "parameters" (Number 1) $ set "induction" (String "Nothing")
        $ set "constructor" (String "bodyPayload") $ set "fields" (toJSON (["bodyPayloadValue"] :: [Text]))
        $ declaration "BodyPayload" "record" (piType True (universeAt (level 0)) (universeAt (level 0)))
      bodyPayloadCtor = set "parameters" (Number 1) $ set "family" (String "BodyPayload")
        $ declaration "bodyPayload" "constructor" (piType True (universeAt (level 0))
          (piType True (varType 0) (object ["term" .= call "BodyPayload" [variable 1 []] []])))
      bodyPayloadField = set "projection" (object ["proper" .= ("BodyPayload" :: Text),"index" .= (2 :: Int)])
        $ declaration "bodyPayloadValue" "function" (piType True (universeAt (level 0))
          (piType True (object ["term" .= call "BodyPayload" [variable 0 []] []]) (varType 1)))
      nat = set "constructors" (toJSON (["zero","suc"] :: [Text])) (declaration "Nat" "datatype" (universeAt (level 0)))
      zeroDef = set "family" (String "Nat") (declaration "zero" "constructor" (named "Nat"))
      sucDef = set "family" (String "Nat") (declaration "suc" "constructor" (signature [named "Nat"] (named "Nat")))
      iterateFn = safe $ set "type" (piType True (universeAt (level 0))
        (fn (fn (varType 0) (varType 0)) (fn (named "Nat") (fn (varType 0) (varType 0)))))
        $ operation "iterate" [] "Bool" $ split 2
          [("zero",0,done 3 (variable 0 [])),("suc",1,done 4 (call "iterate"
            [variable 3 [],variable 2 [],variable 1 [],invoke (variable 2 []) [variable 0 []]] []))]
      iterated = safe $ operation "iterated" ["Bool","Nat","Bool"] "Bool" $ done 3
        (call "iterate" [get "term" (named "Bool"),call "xor" [variable 2 []] [],variable 1 [],variable 0 []] [])
      callbacks = set "induction" (String "Nothing") $ set "constructor" (String "callbacks")
        $ set "fields" (toJSON (["callback"] :: [Text])) (declaration "Callbacks" "record" (universeAt (level 0)))
      callbackCtor = set "family" (String "Callbacks") $ declaration "callbacks" "constructor"
        (fn (fn (named "Bool") (named "Bool")) (named "Callbacks"))
      runCallback = safe $ operation "runCallback" ["Callbacks","Bool"] "Bool"
        (set "eta" (object ["constructor" .= ("callbacks" :: Text),"fields" .= (["callback"] :: [Text])
          ,"branch" .= object ["arity" .= (1 :: Int),"tree" .= done 2 (invoke (variable 1 []) [variable 0 []])]]) (split 0 []))
      recordCaller = safe $ operation "recordCaller" ["Bool","Bool"] "Bool" $ done 2
        (call "runCallback" [constructor "callbacks" [call "xor" [variable 1 []] []],variable 0 []] [])
      treeType = set "constructors" (toJSON (["leaf","branch"] :: [Text])) (declaration "CallbackTree" "datatype" (universeAt (level 0)))
      leafCtor = set "family" (String "CallbackTree") $ declaration "leaf" "constructor"
        (fn (fn (named "Bool") (named "Bool")) (named "CallbackTree"))
      branchCtor = set "family" (String "CallbackTree") $ declaration "branch" "constructor"
        (signature [fn (named "Bool") (named "Bool"),named "CallbackTree",named "CallbackTree"] (named "CallbackTree"))
      -- The case tree retains a runtime predicate result, while callback
      -- nodes are known. This cannot be solved by head reduction alone.
      evaluateTree = safe $ operation "evaluateTree" ["CallbackTree","Bool"] "Bool" $ split 0
        [("leaf",1,done 2 (invoke (variable 1 []) [variable 0 []]))
        ,("branch",3,done 4 (call "selectTree" [invoke (variable 3 []) [variable 0 []]
          ,variable 2 [],variable 1 [],variable 0 []] []))]
      selectTree = safe $ operation "selectTree" ["Bool","CallbackTree","CallbackTree","Bool"] "Bool" $ split 0
        [("true",0,done 3 (call "evaluateTree" [variable 2 [],variable 0 []] []))
        ,("false",0,done 3 (call "evaluateTree" [variable 1 [],variable 0 []] []))]
      treeCaller = safe $ operation "treeCaller" ["Bool","Bool","Bool"] "Bool" $ done 3
        (call "evaluateTree" [constructor "branch" [call "xor" [variable 2 []] []
          ,constructor "leaf" [call "xor" [variable 1 []] []]
          ,constructor "leaf" [object ["tag" .= ("lambda" :: Text),"abstraction" .= object ["binds" .= True,"body" .= variable 0 []]]]]
          ,variable 0 []] [])
      additions = [applyOnce,xor,caller,lambdaCaller,bodyOnlyType,bodyOnlyCaller,chooseSchema,bodyPayload,bodyPayloadCtor,bodyPayloadField,nat,zeroDef,sucDef,iterateFn,iterated
        ,callbacks,callbackCtor,runCallback,recordCaller,treeType,leafCtor,branchCtor,evaluateTree,selectTree,treeCaller]
      added = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      registry = set "nat" (String "Nat") $ set "zero" (String "zero") $ set "suc" (String "suc") (get "builtins" (document base))
      inv = base {declarations = M.adjust (set "constructors" (toJSON (["true","false"] :: [Text]))) "Bool" $ M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
        ,document = set "checking" (toJSON [object ["module" .= ("Checked" :: Text),"safe" .= True,"terminationCheck" .= True]]) (set "builtins" registry (document base))
        ,modelRequirements = M.map (`S.union` added) (modelRequirements base)}
      prepared = P.prepare inv
      expanded = P.inventory prepared
      finite = M.fromList [(s,d) | (s,v) <- M.toList (declarations expanded),Right d <- [F.domain expanded v]]
      shapes = fst (A.discover expanded finite)
      calculations = A.functions expanded finite shapes
      table = M.mapMaybe (either (const Nothing) Just) calculations
  check (all (`M.notMember` P.failures prepared) ["closureCaller","lambdaCaller","iterated","recordCaller","treeCaller"]) (show (P.failures prepared))
  forM_ ["closureCaller","lambdaCaller","recordCaller"] $ \name -> do
    calculation <- either (fail . show) pure (calculations M.! name)
    forM_ [False,True] $ \captured -> forM_ [False,True] $ \argument ->
      check (evalWith table [B captured,B argument] (A.body calculation) == B (captured /= argument)) "closure specialization lost a capture or argument"
  check (length [i | i <- P.instances prepared,P.origin i == "applyOnce"] == 2) "closure templates were merged or specialized by runtime value"
  let bodyOnlyInventory = inv
        { document = set "selectionProfile" (String "declarations") $ set "library" (String "fixture")
            $ set "modules" (toJSON [object ["name" .= ("Checked" :: Text)
              ,"source" .= object ["library" .= ("fixture" :: Text)],"definitions" .= [bodyOnlyCaller]]]) (document inv)
        , modelRequirements = modelRequirements inv }
      bodyOnlyPrepared = P.prepare bodyOnlyInventory
      bodyOnlyExpanded = P.inventory bodyOnlyPrepared
      bodyOnlyInstances = [d | d <- M.elems (declarations bodyOnlyExpanded)
        ,get "higherOrderOrigin" d == String "bodyOnlyType"]
  check (not (null bodyOnlyInstances) && all ((== [0]) . P.nativeParameters) bodyOnlyInstances)
    ("static body-only extent was omitted because it is absent from the closure signature: "
      ++ show (map (\d -> (get "name" d,P.nativeParameters d,get "closureSpecialization" d)) bodyOnlyInstances,P.failures bodyOnlyPrepared))
  let bodyOnlyShapes = fst (A.discover bodyOnlyExpanded finite)
      bodyOnlyCalculations = A.functions bodyOnlyExpanded finite bodyOnlyShapes
  forM_ bodyOnlyInstances $ \d -> do
    calculation <- either (fail . show) pure (bodyOnlyCalculations M.! string (get "name" d))
    let rendered = Text.unlines (A.renderCalculation bodyOnlyExpanded bodyOnlyShapes id calculation)
    check ("in 'typeArgument0'" `Text.isInfixOf` rendered)
      "schema-builder calculation failed to declare its body-only extent"
  treeCalculation <- either (fail . show) pure (calculations M.! "treeCaller")
  forM_ [False,True] $ \guardCapture -> forM_ [False,True] $ \effectCapture -> forM_ [False,True] $ \argument ->
    check (evalWith table [B guardCapture,B effectCapture,B argument] (A.body treeCalculation)
      == B (if guardCapture /= argument then effectCapture /= argument else argument))
      "static tree specialization changed predicate/effect captures or branch choice"
  check (M.member "runCallback" (P.failures prepared) && M.member "evaluateTree" (P.failures prepared))
    "unknown runtime callbacks were admitted"
  let monomorphicInventory = inv {modelRequirements = M.singleton "monomorphic"
        (S.fromList [("recordCaller","behavior"),("runCallback","behavior"),("xor","behavior"),("Callbacks","structure"),("Bool","structure")])}
      monomorphicPrepared = P.prepare monomorphicInventory
      monomorphicExpanded = P.inventory monomorphicPrepared
      monomorphicShapes = fst (A.discover monomorphicExpanded finite)
      monomorphicCalculations = A.functions monomorphicExpanded finite monomorphicShapes
  check (M.notMember "recordCaller" (P.failures monomorphicPrepared)
    && either (const False) (const True) (monomorphicCalculations M.! "recordCaller"))
    "a monomorphic callback record incorrectly depended on an unrelated generic template"
  let malformed = inv {declarations = M.adjust (set "compiled" (done 2
        (call "runCallback" [constructor "leaf" [lambda],variable 0 []] []))) "recordCaller" (declarations inv)}
  check (M.member "recordCaller" (P.failures (P.prepare malformed))) "wrong-carrier static constructor was admitted"
  let altered declarationName change = inv {declarations = M.adjust change declarationName (declarations inv)}
      badArity = altered "recordCaller" (set "compiled" (done 2
        (call "runCallback" [constructor "callbacks" [],variable 0 []] [])))
  check (M.member "recordCaller" (P.failures (P.prepare badArity))) "static record payload arity was guessed"
  forM_ [set "opaque" (Bool True),set "terminates" (Bool False),set "compiled" Null] $ \change ->
    check (M.member "recordCaller" (P.failures (P.prepare (altered "runCallback" change))))
      "opaque, unchecked or missing callback computation was admitted"
  let bindingEvidence = set "closureSpecialization" (object ["types" .= map P.typeValue
        [P.Open 2 (P.LevelExpr 0 M.empty),P.OpenFamily 1 [P.Open 0 (P.LevelExpr 0 M.empty)] (P.LevelExpr 0 M.empty)]]) (object [])
  check (P.nativeParameters bindingEvidence == [0,2] && map fst (P.nativeFamilies bindingEvidence) == [1])
    "generated callback signature lost open capture/result bindings"
  let constrained = set "closureIndexEquations" (toJSON [object ["domain" .= named "Bool"
        ,"left" .= variable 0 [],"right" .= constructor "true" []]])
        (safe $ operation "constrained" ["Bool"] "Bool" (done 1 (variable 0 [])))
      constrainedInv = inv {declarations = M.insert "constrained" constrained (declarations inv)
        ,modelRequirements = M.singleton "constraint" (S.singleton ("constrained","behavior"))}
      constrainedOutput = T.generate constrainedInv
  check (isLeft (F.function constrainedInv finite constrained)) "finite lowering discarded a static container precondition"
  check ("assert constraint" `Text.isInfixOf` T.modelText constrainedOutput
    && " == true" `Text.isInfixOf` T.modelText constrainedOutput)
    "Boolean lowering discarded a static container precondition"
  let onlyInConstraint = set "closureIndexEquations" (toJSON [object ["domain" .= named "Bool"
        ,"left" .= call "xor" [variable 1 [],variable 0 []] [],"right" .= constructor "true" []]])
        (safe $ operation "constrained" ["Bool","Bool"] "Bool" (done 2 (variable 0 [])))
      refs names = object ["symbols" .= (names :: [Text])]
      selectedDocument = set "models" (object ["constraint" .= object ["state" .= refs ["Bool"]
        ,"commands" .= refs ["Bool"],"transition" .= object ["entry" .= refs ["constrained"]]]]) (document inv)
      selectedInventory = constrainedInv {document = selectedDocument
        ,declarations = M.insert "constrained" onlyInConstraint (declarations inv)
        ,modelRequirements = M.singleton "constraint" (S.fromList [("Bool","structure"),("constrained","behavior")
          ,("xor","behavior"),("applyOnce","behavior")])}
      selectedPrepared = P.prepare selectedInventory
  check (S.member "xor" (P.runtimeClosure selectedPrepared))
    ("a computation used only by a static container precondition disappeared from the runtime closure: "
      ++ show (P.failures selectedPrepared,P.runtimeClosure selectedPrepared))

  iteration <- either (fail . show) pure (calculations M.! "iterated")
  forM_ [False,True] $ \captured -> forM_ [0..7] $ \n -> forM_ [False,True] $ \value ->
    check (evalWith table [B captured,Z n,B value] (A.body iteration)
      == B (if odd n then captured /= value else value)) "recursive closure cache lost its body or captured value"

  let retainedOnly = declaration "sourceOnly" "axiom" (universeAt (level 0))
      refs xs = object ["symbols" .= (xs :: [Text])]
      model roots = object ["models" .= object ["selected" .= object
        ["state" .= refs ["Bool"],"commands" .= refs ["Bool"]
        ,"transition" .= object ["entry" .= refs roots]]]]
      addModels roots = set "models" (get "models" (model roots)) (document inv)
      accounting roots = inv {document = addModels roots
        ,declarations = M.insert "sourceOnly" retainedOnly (declarations inv)
        ,modelRequirements = M.map (S.insert ("sourceOnly","structure")) (modelRequirements inv)}
      retainedReport = T.generate (accounting ["closureCaller"])
      accountingRows = array (get "obligations" (T.correspondence retainedReport))
  check (T.complete retainedReport) (show (T.diagnostics retainedReport))
  forM_ [row | row <- accountingRows,"@closure-" `Text.isInfixOf` string (get "symbol" row)] $ \row ->
    check (M.member (string (get "checkedDefinition" (get "source" row))) (declarations inv))
      "closure obligation points to a generated identity absent from the source inventory"
  check (any (\row -> get "symbol" row == String "sourceOnly" && get "kind" row == String "reduction-source"
    && get "sourceKind" row == String "structure" && get "target" row == Null) accountingRows)
    "unneeded source evidence was omitted or presented as native behavior"
  check (not (T.complete (T.generate (accounting ["closureCaller","sourceOnly"]))))
    "an explicitly selected unsupported root was waived as reduced source"
  let brokenAccounting = (accounting ["closureCaller"]) {declarations = M.adjust (set "compiled" Null) "xor" (declarations (accounting ["closureCaller"]))}
  check (not (T.complete (T.generate brokenAccounting))) "an unresolved runtime dependency was waived as reduced source"

sequenceChecks :: Inventory -> IO ()
sequenceChecks base = do
  let sequenceType = set "nativeSequence" (named "Nat") $ set "constructors" (toJSON (["nil","cons"] :: [Text]))
        $ declaration "ListNat" "datatype" (universeAt (level 0))
      nil = set "family" (String "ListNat") (declaration "nil" "constructor" (named "ListNat"))
      cons = set "family" (String "ListNat") (declaration "cons" "constructor" (signature [named "Nat",named "ListNat"] (named "ListNat")))
      shift = set "terminates" (Bool True) $ set "sourceModule" (String "Checked") $
        operation "shift" ["Nat","ListNat"] "ListNat" (split 1
          [("nil",0,done 1 (constructor "nil" [])),("cons",2,done 3 (constructor "cons"
            [call "add" [variable 2 [],variable 1 []] [],call "shift" [variable 2 [],variable 0 []] []]))])
      additions = [sequenceType,nil,cons,shift]
      extra = S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- additions]
      inv = base {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- additions]) (declarations base)
        ,document = set "checking" (toJSON [object ["module" .= ("Checked" :: Text),"safe" .= True,"terminationCheck" .= True]]) (document base)
        ,modelRequirements = M.map (`S.union` extra) (modelRequirements base)}
      (shapes,errors) = A.discover inv M.empty
      calculations = A.functions inv M.empty shapes
      list values = R "ListNat" (M.singleton "items" (Seq (map Z values)))
  check (M.null errors && M.member "ListNat" shapes) (show errors)
  table <- traverse (either (fail . show) pure) calculations
  forM_ [[],[0],[2,2,0],[10^(80 :: Int),3,3]] $ \values ->
    forM_ [0,1,10^(70 :: Int)] $ \offset ->
      check (evalWith table [Z offset,list values] (A.body (table M.! "shift")) == list (map (+offset) values))
        "recursive sequence translation changed order, multiplicity, capture, or arithmetic"
  let unchecked = inv {document = document base}
      broken = inv {declarations = M.adjust (set "primitive" (String "Unsupported")) "add" (declarations inv)}
  check (isLeft (A.functions unchecked M.empty shapes M.! "shift")) "recursive function flag alone admitted a call cycle"
  check (isLeft (A.functions broken M.empty shapes M.! "shift")) "recursive cycle concealed a refused external dependency"

  -- Recognize structural equations at arbitrary identities, not a library
  -- function name. The consuming family is admitted only after its helper.
  forM_ ["join","combine"] $ \helper -> do
    let joinedType index = object ["term" .= call "Joined" [index] []]
        joined = set "constructors" (toJSON (["joined"] :: [Text])) $
          declaration "Joined" "datatype" (signature [named "ListNat"] (universeAt (level 0)))
        constructorDef = set "family" (String "Joined") $
          declaration "joined" "constructor" (signature [named "ListNat",named "ListNat"]
            (joinedType (call helper [variable 1 [],variable 0 []] [])))
        helperDef headValue = set "terminates" (Bool True) $ set "sourceModule" (String "Checked") $
          operation helper ["ListNat","ListNat"] "ListNat" (split 0
            [("nil",0,done 1 (variable 0 [])),("cons",2,done 3 (constructor "cons"
              [headValue,call helper [variable 1 [],variable 0 []] []]))])
        add definitions = inv {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- definitions]) (declarations inv)
          ,modelRequirements = M.map (`S.union` S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- definitions]) (modelRequirements inv)}
        valid = add [joined,constructorDef,helperDef (variable 2 [])]
        (admitted,refused) = A.discover valid M.empty
        calcs = A.functions valid M.empty admitted
    check (M.member "Joined" admitted && M.notMember "Joined" refused) "structural index helper failed stratified admission"
    helperCalc <- either (fail . show) pure (calcs M.! helper)
    native <- traverse (either (fail . show) pure) calcs
    forM_ [[],[0],[2,2,0]] $ \left -> forM_ [[],[1],[2,2]] $ \right ->
      check (evalWith native [list left,list right] (A.body helperCalc) == list (left ++ right)) "named structural helper changed concatenation"
    let one = object ["tag" .= ("literal" :: Text),"literal" .= object ["tag" .= ("natural" :: Text),"value" .= (1 :: Integer)]]
        modified = add [joined,constructorDef,helperDef (call "add" [variable 2 [],one] [])]
        noEvidence = valid {document = document base}
        signatureOnly = valid {declarations = M.adjust (set "compiled" Null) helper (declarations valid)}
    forM_ [modified,noEvidence,signatureOnly] $ \invalid ->
      check (M.notMember "Joined" (fst (A.discover invalid M.empty))) "unjustified recursive index equation admitted"
    let joinedSchema = joinedType (call helper [variable 1 [],variable 0 []] [])
        implicitRead = set "projection" (object ["proper" .= Null,"index" .= (3 :: Int)]) $
          set "type" (signature [named "ListNat",named "ListNat",joinedSchema] (named "Nat")) $
          operation "implicitRead" [] "Nat" (done 1 one)
        fixedSchema = joinedType (call helper [constructor "nil" [],constructor "nil" []] [])
        recoverCaller = set "type" (signature [fixedSchema] (named "Nat")) $
          operation "recoverJoined" [] "Nat" (done 1 (call "implicitRead" [variable 0 []] []))
        recovery = add [joined,constructorDef,helperDef (variable 2 []),implicitRead,recoverCaller]
        recoveryShapes = fst (A.discover recovery M.empty)
    check (isLeft (A.functions recovery M.empty recoveryShapes M.! "recoverJoined"))
      "concatenation result was used to recover an unjustified split of its inputs"

  forM_ ["bump","incrementList"] $ \helper -> do
    let mappedType index = object ["term" .= call "MappedList" [index] []]
        mapped = set "constructors" (toJSON (["mappedList"] :: [Text])) $
          declaration "MappedList" "datatype" (signature [named "ListNat"] (universeAt (level 0)))
        mappedCtor = set "family" (String "MappedList") $ declaration "mappedList" "constructor"
          (signature [named "ListNat"] (mappedType (call helper [variable 0 []] [])))
        one = object ["tag" .= ("literal" :: Text),"literal" .= object ["tag" .= ("natural" :: Text),"value" .= (1 :: Integer)]]
        helperDef tailArgument = set "terminates" (Bool True) $ set "sourceModule" (String "Checked") $
          operation helper ["ListNat"] "ListNat" (split 0
            [("nil",0,done 0 (constructor "nil" [])),("cons",2,done 2 (constructor "cons"
              [call "add" [variable 1 [],one] [],call helper [tailArgument] []]))])
        add definitions = inv {declarations = M.union (M.fromList [(string (get "name" d),d) | d <- definitions]) (declarations inv)
          ,modelRequirements = M.map (`S.union` S.fromList [(string (get "name" d),if get "kind" d == String "function" then "behavior" else "structure") | d <- definitions]) (modelRequirements inv)}
        valid = add [mapped,mappedCtor,helperDef (variable 0 [])]
        admitted = fst (A.discover valid M.empty)
    check (M.member "MappedList" admitted) "structural list map failed computed-index admission"
    native <- traverse (either (fail . show) pure) (A.functions valid M.empty admitted)
    forM_ [[],[0],[2,2,0],[10^(80 :: Int),3,3]] $ \values ->
      check (evalWith native [list values] (A.body (native M.! helper)) == list (map (+1) values))
        "computed-index list map lost values, order, or repeated positions"
    let wrongTail = add [mapped,mappedCtor,helperDef (constructor "cons" [variable 1 [],variable 0 []])]
        uncheckedMap = valid {document = document base}
        missingBody = valid {declarations = M.adjust (set "compiled" Null) helper (declarations valid)}
    forM_ [wrongTail,uncheckedMap,missingBody] $ \invalid ->
      check (M.notMember "MappedList" (fst (A.discover invalid M.empty)))
        "unjustified recursion was admitted by the structural list-map rule"

-- Default selection must cover independent definitions and must not infer proof
-- roles from a declaration's spelling or from a local annotation.
automaticSelectionChecks :: IO ()
automaticSelectionChecks = do
  let clean = set "statementDependencies" (toJSON ([] :: [Text]))
        . set "bodyDependencies" (toJSON ([] :: [Text]))
      ordinary = clean (operation "step-preserves" ["Bool"] "Bool" (done 1 (variable 0 [])))
      negation = clean (operation "not" ["Bool"] "Bool" (split 0
        [("true",0,done 0 (constructor "false" [])),("false",0,done 0 (constructor "true" []))]))
      proof = clean (operation "identity-law" ["Bool"] "Equality" (done 1 (constructor "refl" [])))
      opaque = clean (declaration "opaque" "axiom" (signature [named "Bool"] (named "Bool")))
      md libraryName ds = object ["name" .= libraryName,"source" .= object ["library" .= libraryName]
        ,"definitions" .= ds]
      input = object ["selectionProfile" .= ("declarations" :: Text),"library" .= ("Own" :: Text)
        ,"builtins" .= object ["bool" .= ("Bool" :: Text),"true" .= ("true" :: Text)
          ,"false" .= ("false" :: Text),"equality" .= ("Equality" :: Text)]
        ,"modules" .= [md ("Own" :: Text) [ordinary,negation,proof,opaque],md ("Dependency" :: Text)
          [clean (declaration "Bool" "datatype" (universeAt (level 0)))
          ,clean (declaration "Equality" "datatype" (universeAt (level 0)))
          ,clean (operation "unrelated" ["Bool"] "Bool" (done 1 (variable 0 [])))]]]
      emptyMapping = Mapping.Mapping 2 "Own" "own.agda-lib" ["Own"] False M.empty
  selected <- either (fail . Text.unpack) pure (prepare emptyMapping input)
  let needs = required selected
  check (S.member ("not","behavior") needs && S.member ("step-preserves","behavior") needs)
    "automatic selection omitted an independent calculation or classified a proof by its name"
  check (S.member ("identity-law","statement") needs && S.member ("identity-law","proof-source") needs
    && not (S.member ("identity-law","behavior") needs)) "canonical equality law lost its proof-source role"
  check (not (S.member ("unrelated","behavior") needs)) "unrelated dependency became project scope"
  check (S.member ("opaque","behavior") needs && S.member ("opaque","external-assumption") needs)
    "assumption provenance replaced a postulated operation's computational requirement"
  let opaqueRows = [r | r <- array (get "obligations" (T.correspondence (T.generate selected)))
                     ,get "symbol" r == String "opaque",get "kind" r == String "behavior"]
  check (not (null opaqueRows) && all ((== String "textual") . get "status") opaqueRows)
    "retaining an assumption concealed an operation with no executable body"
  let model = Mapping.Model "Own" "Local" (Mapping.NamedState "Bool") Nothing
        (Mapping.Function "not" Nothing (Mapping.Position 0) Mapping.DirectState) [] ["step-preserves"]
      overlay = emptyMapping {Mapping.models = M.singleton "local" model}
      refs = [object ["reference" .= name,"candidates" .= [name]] | name <- ["not","Bool","step-preserves"] :: [Text]]
      inputAnnotated = set "resolutions" (toJSON [object ["model" .= ("local" :: Text),"references" .= refs]]) input
  annotated <- either (fail . Text.unpack) pure (prepare overlay inputAnnotated)
  check (needs `S.isSubsetOf` required annotated && S.member ("step-preserves","behavior") (required annotated))
    "a local theorem annotation removed a default computational requirement"
