{-# LANGUAGE OverloadedStrings #-}
module Main where

import Agda2SysML.SourceAlignment
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Position (noRange)
import Agda.TypeChecking.Monad (runTCMTop, freshName)
import Control.Monad (unless)
import Data.Aeson
import Data.Either (isLeft, isRight)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

check :: Bool -> String -> IO ()
check ok message = unless ok (fail message)

main :: IO ()
main = do
  names <- runTCMTop $ do
    a <- freshName noRange "same"
    b <- freshName noRange "same"
    pure (A.QName (A.MName []) a,A.QName (A.MName []) b)
  (f,g) <- either (fail . show) pure names
  let outer = ("M",10)
      inner = ("M",20)
      env = M.fromList [(outer,1),(inner,0)]
      var site key = Direct (String key) (Bound site) []
      source = Direct "call" (Global f) [var outer "first",var inner "second"]
      app q xs = I.Def q [I.Apply (defaultArg x) | x <- xs]
      good = app f [I.Var 1 [],I.Var 0 []]
      expected = [([],"call"),(["eliminations",Number 0,"argument","value"],"first")
        ,(["eliminations",Number 1,"argument","value"],"second")]
  check (matchTerm env source good == Right expected) "resolved binders or argument paths were lost"
  check (isLeft (matchTerm env source (app g [I.Var 1 [],I.Var 0 []]))) "same spelling substituted for canonical identity"
  check (isLeft (matchTerm env source (app f [I.Var 0 [],I.Var 1 []]))) "shadowed binders were swapped"
  check (isLeft (matchTerm (M.singleton outer 1) source good)) "missing local binder guessed"
  check (isLeft (matchTerm env source (app f [I.Var 1 []]))) "missing argument inferred"
  let hiddenCall = I.Def f [I.Apply (setHiding Hidden (defaultArg (I.Var 1 []))),I.Apply (defaultArg (I.Var 0 []))]
  check (isLeft (matchTerm env source hiddenCall)) "hidden insertion was silently admitted"
  let repeated = Direct "repeat" (Global f) [var outer "left",var outer "right"]
  check (fmap (map snd) (matchTerm env repeated (app f [I.Var 1 [],I.Var 1 []])) == Right ["repeat","left","right"])
    "equal terms collapsed distinct source uses"
  check (isLeft (matchTerm env (Direct "higher-order" (Bound inner) [var outer "arg"]) (I.Var 0 [I.Apply (defaultArg (I.Var 1 []))])))
    "higher-order source was admitted by the direct rule"
  let typ t = I.El (I.mkType 0) t
      namedType q = Carrier (Direct "type-name" (Global q) [])
      arrow binder domain result = Arrow "arrow" defaultArgInfo binder domain result
      checkedArrow binds domain result = typ (I.Pi (I.defaultDom domain) ((if binds then I.Abs else I.NoAbs) "_" result))
      atom = typ (app f [])
      dependent = arrow (Just outer) (namedType f)
        (arrow Nothing (namedType f) (Carrier (Direct "family" (Global g) [var outer "index"])))
      before = checkedArrow True atom (checkedArrow False atom (typ (app g [I.Var 0 []])))
      after = checkedArrow True atom (checkedArrow True atom (typ (app g [I.Var 1 []])))
      wrong = checkedArrow True atom (checkedArrow True atom (typ (app g [I.Var 0 []])))
  check (isRight (matchSignature dependent before) && isRight (matchSignature dependent after))
    "signature matching confused Abs/NoAbs binder stacks"
  check (isLeft (matchSignature dependent wrong)) "signature matching kept a raw index after binder insertion"
  check (isLeft (matchSignature (namedType f) (typ (app g [])))) "signature matched a same-spelling different canonical type"
  check (isLeft (matchSignature (arrow Nothing (arrow Nothing (namedType f) (namedType f)) (namedType f))
    (checkedArrow False (checkedArrow False atom atom) atom))) "higher-order signature admitted"
  let hiddenType = typ (I.Pi (setHiding Hidden (I.defaultDom atom)) (I.NoAbs "_" atom))
  check (isLeft (matchSignature (arrow Nothing (namedType f) (namedType f)) hiddenType)) "implicit signature insertion admitted"
  check (isLeft (matchSignature dependent (checkedArrow False atom (typ (app g [I.Var 0 []])))))
    "omitted signature binder was guessed"
  let projectionSource = Parenthesized "projection-parens" (Direct "projection-call" (Global f) [var outer "receiver"])
      projectionType = arrow (Just outer) (namedType f)
        (arrow Nothing (namedType f) (Carrier (Direct "family" (Global g) [projectionSource])))
      projectedType binds i q es = checkedArrow True atom (checkedArrow binds atom (typ (app g [I.Var i (I.Proj ProjPrefix q : es)])))
      projectionBefore = projectedType False 0 f []
      projectionAfter = projectedType True 1 f []
      admit = matchConstructorSignature (S.singleton f) projectionType
  check (isRight (admit projectionBefore) && isRight (admit projectionAfter))
    "constructor signature lost explicit projection or receiver rebasing"
  check (isLeft (admit (projectedType True 0 f []))) "projection receiver captured the newly inserted binder"
  check (isLeft (admit (projectedType False 0 g []))) "projection matched another canonical field with the same spelling"
  check (isLeft (matchConstructorSignature S.empty projectionType projectionBefore)) "projection admitted without checked proper-field evidence"
  check (isLeft (matchSignature projectionType projectionBefore)) "projection rule escaped constructor signature scope"
  check (isLeft (matchTerm (M.singleton outer 0) projectionSource (I.Var 0 [I.Proj ProjPrefix f])))
    "projection rule escaped into direct body matching"
  check (isLeft (admit (projectedType False 0 f [I.Proj ProjPrefix f]))) "nested projection admitted by single-field rule"
  check (isLeft (admit (projectedType False 0 f [I.Apply (defaultArg (I.Var 0 []))]))) "applied projected value silently admitted"
  case admit projectionBefore of
    Left reason -> fail (show reason)
    Right links -> do
      check (any (\(_,sourceId,_) -> sourceId == "projection-call") links) "whole projection expression has no link"
      check (all (\(_,sourceId,_) -> sourceId /= "receiver") links) "invented a bare receiver node in the checked tree"
  putStrLn "canonical identity, binder shadowing, explicit spine and occurrence checks passed"
