{-# LANGUAGE OverloadedStrings #-}
module Main where

import Agda2SysML.Inventory
import qualified Agda2SysML.Diagnostic as D
import qualified Agda2SysML.FiniteTarget as F
import qualified Agda2SysML.Target as T
import qualified Agda2SysML.RelationTarget as R
import Control.Monad (unless, forM_, replicateM)
import Data.Aeson
import Data.Either (isLeft)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text.IO as Text
import System.Environment (getArgs, getEnv)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (callProcess)

main :: IO ()
main = do
  let cs = ["a","b","c"] :: [Text]
      named s = object ["term" .= object ["tag" .= ("definition" :: Text), "symbol" .= s, "eliminations" .= ([] :: [Value])]]
      datatype = object ["name" .= ("Domain" :: Text),"displayName" .= ("Domain" :: Text)
        ,"kind" .= ("datatype" :: Text),"abstract" .= False,"parameters" .= (0 :: Int)
        ,"type" .= object ["term" .= object ["tag" .= ("sort" :: Text)]],"constructors" .= cs]
      constructor c = object ["name" .= c,"displayName" .= c,"kind" .= ("constructor" :: Text),"type" .= named ("Domain" :: Text)]
      literal c = object ["tag" .= ("constructor" :: Text),"symbol" .= c,"eliminations" .= ([] :: [Value])]
      done binders body = object ["tag" .= ("done" :: Text),"binders" .= replicate binders Null,"body" .= body]
      branch c result = object ["symbol" .= c,"branch" .= object ["arity" .= (0 :: Int),"tree" .= done 0 (literal result)]]
      branches = zipWith branch cs (["c","a","b"] :: [Text])
      split alternatives = object ["tag" .= ("case" :: Text),"argument" .= object ["value" .= (0 :: Int)]
        ,"copattern" .= False,"eta" .= Null,"literals" .= ([] :: [Value]),"catchall" .= Null
        ,"lazy" .= False,"fallThrough" .= False,"constructors" .= alternatives]
      signature = object ["term" .= object ["tag" .= ("pi" :: Text),"domain" .= object ["type" .= named ("Domain" :: Text)]
        ,"codomain" .= object ["body" .= named ("Domain" :: Text)]]]
      piType body = object ["term" .= object ["tag" .= ("pi" :: Text),"domain" .= object ["type" .= named ("Domain" :: Text)]
        ,"codomain" .= object ["body" .= body,"binds" .= True]]]
      relationType = piType (piType (object ["term" .= object ["tag" .= ("sort" :: Text)]]))
      relationDecl = object ["name" .= ("Step" :: Text),"displayName" .= ("Step" :: Text)
        ,"kind" .= ("datatype" :: Text),"abstract" .= False,"parameters" .= (0 :: Int)
        ,"type" .= relationType,"constructors" .= (["advance","stay"] :: [Text])]
      relationResult before after = object ["term" .= object ["tag" .= ("definition" :: Text),"symbol" .= ("Step" :: Text)
        ,"eliminations" .= [object ["tag" .= ("apply" :: Text),"argument" .= object ["value" .= v]] | v <- [before,after]]]]
      witness = object ["tag" .= ("variable" :: Text),"index" .= (0 :: Int),"eliminations" .= ([] :: [Value])]
      relationConstructor c ty = object ["name" .= c,"displayName" .= c,"kind" .= ("constructor" :: Text),"type" .= ty]
      advance = relationConstructor ("advance" :: Text) (relationResult (literal ("a" :: Text)) (literal ("b" :: Text)))
      stay = relationConstructor ("stay" :: Text) (piType (relationResult witness witness))
      operation tree = object ["name" .= ("rotate" :: Text),"displayName" .= ("rotate" :: Text)
        ,"kind" .= ("function" :: Text),"sourceSyntax" .= [object []],"type" .= signature,"compiled" .= tree]
      defs = M.fromList ([("Domain",datatype),("rotate",operation (split branches))
        ,("Step",relationDecl),("advance",advance),("stay",stay)] ++ [(c,constructor c) | c <- cs])
      inv = Inventory (object []) defs M.empty (M.singleton "model"
        (S.fromList (("rotate","behavior"):("Step","behavior"):[(c,"structure") | c <- ["Step","advance","stay","Domain"] ++ cs])))
      check ok message = unless ok (fail message)
  shape <- either (fail . show) pure (F.domain inv datatype)
  let domains = M.singleton "Domain" shape
  rel <- either (fail . show) pure (R.relation inv domains relationDecl)
  check (length (R.rules rel) == 2) "relation alternatives disappeared"
  bindingChecks inv domains relationDecl
  check (isLeft (F.function inv domains (operation (split (take 2 branches))))) "missing constructor accepted"
  check (isLeft (F.function inv domains (operation (split (take 1 branches ++ branches))))) "duplicate constructor accepted"
  let bad = inv {declarations = M.insert "a" (object ["kind" .= ("constructor" :: Text),"type" .= signature]) defs}
  check (isLeft (F.domain bad datatype)) "payload constructor collapsed to an enum"
  let generated = T.generate inv
  check (T.complete generated) (show (T.diagnostics generated))
  options <- getArgs
  unless (options `elem` [[],["--compiler-only"]]) (fail "Expected --compiler-only or no test options")
  unless (options == ["--compiler-only"]) $ do
    root <- getEnv "AGDA2SYSML_TEST_VALIDATOR"
    java <- getEnv "AGDA2SYSML_TEST_JAVA"
    withSystemTempDirectory "finite-target" $ \directory -> do
      let file = directory </> "model.sysml"
          library = root </> "share/agda2sysml-validator/sysml"
      Text.writeFile file (T.modelText generated)
      callProcess (root </> "bin/agda2sysml-validate") [file]
      callProcess java ["--class-path",library </> "jupyter-sysml-kernel-0.58.0-all.jar"
        ,"test/TargetEvaluation.java",library </> "sysml.library",file
        ,"'rotate'('Domain'::'a') == 'Domain'::'c'","true"
        ,"'rotate'('Domain'::'b') == 'Domain'::'a'","true"
        ,"'rotate'('Domain'::'c') == 'Domain'::'b'","true"
        ,"'Domain'::'a' == 'Domain'::'b'","false"
        ,"'advance'('Domain'::'a', 'Domain'::'b')","true"
        ,"'advance'('Domain'::'b', 'Domain'::'a')","false"
        ,"'stay'('Domain'::'c', 'Domain'::'c', 'Domain'::'c')","true"
        ,"'stay'('Domain'::'a', 'Domain'::'b', 'Domain'::'c')","false"
        ,"'Step'('Domain'::'a', 'Domain'::'b')","true"]
  putStrLn (if options == ["--compiler-only"] then "finite-domain compiler checks passed; Pilot skipped" else "finite-domain rejection and native evaluation checks passed")

-- Exercise every layout up to five arguments and every finite value tuple.
-- Equal witness types deliberately prevent carrier checking from masking a
-- wrong slot. This evaluator observes generated endpoints independently.
bindingChecks :: Inventory -> M.Map Text F.Domain -> Value -> IO ()
bindingChecks base domains relationDecl = do
  let named s = object ["term" .= object ["tag" .= ("definition" :: Text),"symbol" .= (s :: Text)
        ,"eliminations" .= ([] :: [Value])]]
      piType flag domain out = object ["term" .= object ["tag" .= ("pi" :: Text)
        ,"domain" .= object ["type" .= named domain]
        ,"codomain" .= object ["binds" .= flag,"body" .= out]]]
      ref i = object ["tag" .= ("variable" :: Text),"index" .= (i :: Int),"eliminations" .= ([] :: [Value])]
      result value = object ["term" .= object ["tag" .= ("definition" :: Text),"symbol" .= ("Step" :: Text)
        ,"eliminations" .= [object ["tag" .= ("apply" :: Text),"argument" .= object ["value" .= value]] | _ <- [0,1 :: Int]]]]
      construct layout value = foldr (\flag out -> piType (Bool flag) "Domain" out) (result value) layout
      run typ = R.relation (base {declarations = M.insert "stay"
        (object ["name" .= ("stay" :: Text),"kind" .= ("constructor" :: Text),"type" .= typ]) (declarations base)}) domains relationDecl
      check ok message = unless ok (fail message)
      rejected kind typ = case run typ of
        Left reason -> D.category reason == kind
        Right _ -> False
      lowered typ = do
        rel <- either (fail . show) pure (run typ)
        case filter ((== "stay") . R.ruleSymbol) (R.rules rel) of
          [r] -> pure r
          _ -> fail "relation rule identity changed"
      evaluate values (R.Witness i) = values !! i
      evaluate _ _ = error "unexpected non-witness endpoint"
  forM_ [0..5] $ \arity -> forM_ (replicateM arity [False,True]) $ \layout -> do
    let bound = length (filter id layout)
    forM_ [0..bound-1] $ \i -> do
      rule <- lowered (construct layout (ref i))
      check (length (R.witnesses rule) == arity) "nonbinding witness was erased"
      forM_ (replicateM arity [0,1,2 :: Int]) $ \values -> do
        let expected = reverse [v | (binds,v) <- zip layout values,binds] !! i
        check (map (evaluate values) (R.endpoints rule) == [expected,expected])
          ("relation endpoint changed under binding layout " ++ show (layout,i,values))
    check (rejected D.Syntax (construct layout (ref bound))) "out-of-scope endpoint accepted"
    check (rejected D.Syntax (construct layout (ref (-1)))) "negative endpoint variable accepted"
  forM_ [Null,String "false",Number 0] $ \flag ->
    check (rejected D.Syntax (piType flag "Domain" (result (ref 0)))) "missing/malformed binding metadata guessed"
  check (rejected D.Representation (piType (Bool True) "Missing" (result (ref 0)))) "unsupported witness carrier admitted"
