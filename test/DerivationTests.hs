{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Agda2SysML.Derivation as D
import Agda2SysML.Inventory
import Control.Monad (unless)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString as BS
import Data.Either (isLeft)
import Data.List (nub)
import qualified Data.Map.Strict as M
import qualified Data.Text.Encoding as TE

check :: Bool -> String -> IO ()
check yes message = unless yes (fail message)

main :: IO ()
main = do
  let term = object ["tag" .= ("variable" :: String),"index" .= (0 :: Int)]
      compiled = object ["uses" .= [term,term]]
      definition = object ["name" .= ("f" :: String),"compiled" .= compiled]
      inv = Inventory Null (M.singleton "f" definition) M.empty M.empty
      annotated = D.annotate "f" "compiled" compiled
      inputs = array (get "uses" annotated)
      marks = [D.origin "native.variable" input Null [] | input <- inputs]
      piece evidence = D.mark "f" "identifier" evidence "'α\\'x'"
      doc = "// λ\n" <> D.mark "f" "call" (D.derived "native.call" [] Null marks)
        ("'outer'(" <> D.joinDoc ", " (map piece marks) <> ")")
      model = D.render doc
      trace = D.report inv inv doc
      targets = array (get "targetOccurrences" trace)
      checked = array (get "checkedOccurrences" trace)
      ids = map (get "id") targets
      occurrences = [t | t <- targets,get "role" t == String "identifier"]
      slice t = let i = case array (get "intervals" t) of { [one] -> one; _ -> error "expected exactly one interval" }
                    number (Number n) = round n
                    number _ = error "missing interval"
                    a = number (get "start" i); b = number (get "end" i)
                in TE.decodeUtf8 (BS.take (b-a) (BS.drop a (TE.encodeUtf8 model)))
  check (D.strip annotated == compiled) "annotation changed checked values"
  check (model == "// λ\n'outer'('α\\'x', 'α\\'x')") "marks changed emitted bytes"
  check (D.validate model trace == Right ()) "valid nested UTF-8 spans rejected"
  check (length ids == length (nub ids) && length occurrences == 2) "equal renderings lost occurrence identity"
  check (all ((== "'α\\'x'") . slice) occurrences) "Unicode or escaping moved a target interval"
  check (length checked == 2 && length (nub (map (get "path") checked)) == 2) "equal checked values collapsed their paths"
  let bad = case trace of Object fs -> Object (KM.insert "artifactDigest" Null fs); _ -> Null
  check (isLeft (D.validate model bad)) "malformed digest accepted"
  let outer = [d | d <- array (get "derivations" trace), length (array (get "inputs" d)) == 2]
  check (not (null outer)) "parent derivation lost a necessary child origin"
  let missing = D.report inv inv (D.mark "f" "bad" (D.derived "native.bad" [D.root "absent" "compiled"] Null []) "x")
  check (isLeft (D.validate "x" missing)) "unresolved checked reference accepted"
  let locators = [get "$occurrence" x | x <- inputs]
      sourceItems = [object ["id" .= s,"module" .= ("M" :: String)] | s <- ["left","right" :: String]]
      links = [object ["checked" .= r,"source" .= s,"clause" .= ("clause" :: String)
        ,"rule" .= ("source.direct-first-order" :: String),"ruleVersion" .= (1 :: Int)]
        | (r,s) <- zip locators ["left","right" :: String]]
      sourceDocument = object ["modules" .= [object ["name" .= ("M" :: String)
        ,"sourceCorrespondence" .= object ["occurrences" .= sourceItems]
        ,"sourceAlignment" .= object ["definitions" .= [object ["unavailable" .= Null,"links" .= links]]]]]]
      original = inv {document = sourceDocument}
      preparedDefinition = case definition of
        Object fs -> Object (KM.insert "preparationOrigin" "f"
          (KM.insert "specializationArguments" (toJSON ([] :: [Value])) fs))
        _ -> error "definition"
      prepared = original {declarations = M.singleton "f" preparedDefinition}
      aligned = D.report original prepared doc
  check (D.validate model aligned == Right ()) "verified preparation transport rejected"
  check (all ((== String "derived") . get "sourcePrecision") (array (get "checkedOccurrences" aligned)))
    "identity preparation discarded independently verified source evidence"
  check (all ((== String "derived") . get "sourcePrecision") (array (get "targetOccurrences" aligned)))
    "source derivation did not compose"
  let changed = case preparedDefinition of Object fs -> Object (KM.insert "compiled" (object ["uses" .= [term]]) fs); _ -> Null
      changedTrace = D.report original (prepared {declarations = M.singleton "f" changed}) doc
  check (all ((== String "unavailable") . get "sourcePrecision") (array (get "checkedOccurrences" changedTrace)))
    "changed preparation retained source paths based on equal subterms"
  let boundaryDoc = D.mark "f" "outer" (D.derived "native.outer" [] Null [])
        (D.mark "f" "generated" (D.generated "native.generated") "g" <> doc)
      boundaryTrace = D.report original prepared boundaryDoc
  check (case array (get "targetOccurrences" boundaryTrace) of
    first:_ -> get "sourcePrecision" first == String "unavailable"
    [] -> False)
    "generated input was promoted by source-aligned siblings"
  let missingNodeOrigin = D.mark "f" "missing-origin" (D.origin "native.direct" term Null []) doc
      missingNodeTrace = D.report original prepared missingNodeOrigin
  check (case array (get "targetOccurrences" missingNodeTrace) of
    first:_ -> get "sourcePrecision" first == String "unavailable"
    [] -> False) "aligned children hid a missing checked origin on their parent"
  let explicitBoundary = D.mark "f" "known-unavailable"
        (D.origin "native.direct" (case inputs of x:_ -> x; _ -> error "missing checked test input") Null [D.generated "native.boundary"]) "x"
      explicitTrace = D.report original prepared explicitBoundary
  check (all ((== String "unavailable") . get "sourcePrecision") (array (get "targetOccurrences" explicitTrace)))
    "attaching a direct checked origin erased an explicit boundary"
  let forged = case explicitTrace of
        Object fs -> Object (KM.insert "targetOccurrences" (toJSON [case t of
          Object fields -> Object (KM.insert "sourcePrecision" "derived" fields)
          _ -> t | t <- array (get "targetOccurrences" explicitTrace)]) fs)
        _ -> Null
  check (isLeft (D.validate "x" forged)) "validator accepted boundary laundering"
  let info = object ["hiding" .= ("explicit" :: String),"relevance" .= ("relevant" :: String),"quantity" .= ("unrestricted" :: String)]
      named :: String -> [Value] -> Value
      named sym args = object ["tag" .= ("definition" :: String),"symbol" .= (sym :: String)
        ,"eliminations" .= [object ["tag" .= ("apply" :: String),"argument" .= object ["info" .= info,"value" .= a]] | a <- args]]
      variable i = object ["tag" .= ("variable" :: String),"index" .= (i :: Int),"eliminations" .= ([] :: [Value])]
      asType t = object ["term" .= t]
      piType binds domain body = object ["term" .= object ["tag" .= ("pi" :: String)
        ,"domain" .= object ["info" .= info,"type" .= domain]
        ,"codomain" .= object ["binds" .= binds,"name" .= ("_" :: String),"body" .= body]]]
      atom = asType (named "A#canonical" [])
      beforeType = piType True atom (piType False atom (asType (named "Family#canonical" [variable 0])))
      afterType = piType True atom (piType True atom (asType (named "Family#canonical" [variable 1])))
      wrongType = piType True atom (piType True atom (asType (named "Family#canonical" [variable 0])))
  check (D.signatureShape beforeType /= Nothing && D.signatureShape beforeType == D.signatureShape afterType)
    "signature transport rejected correct NoAbs/Abs rebasing"
  check (D.signatureShape beforeType /= D.signatureShape wrongType) "signature transport confused telescope slots"
  check (D.signatureShape atom /= D.signatureShape (asType (named "A#different" []))) "signature transport ignored canonical type identity"
  check (D.signatureShape (piType True beforeType atom) == Nothing) "signature transport admitted higher-order domains"
  let project i name = object ["tag" .= ("variable" :: String),"index" .= (i :: Int)
        ,"eliminations" .= [object ["tag" .= ("project" :: String),"symbol" .= (name :: String)]]]
      projected binds i name = piType True atom (piType binds atom (asType (named "Family#canonical" [project i name])))
  check (D.signatureShape (projected False 0 "field#canonical") /= Nothing
    && D.signatureShape (projected False 0 "field#canonical") == D.signatureShape (projected True 1 "field#canonical"))
    "signature projection transport lost the resolved receiver"
  check (D.signatureShape (projected False 0 "field#canonical") /= D.signatureShape (projected True 0 "field#canonical"))
    "signature projection transport captured a different receiver"
  check (D.signatureShape (projected False 0 "field#canonical") /= D.signatureShape (projected False 0 "field#different"))
    "signature projection transport discarded canonical field identity"
  let sigRef = D.root "f" "type"
      sigLink = object ["checked" .= sigRef,"source" .= ("signature-expression" :: String),"signature" .= ("signature" :: String)
        ,"rule" .= ("source.explicit-signature" :: String),"ruleVersion" .= (1 :: Int)]
      sigSource role identifier = object ["id" .= (identifier :: String),"module" .= ("M" :: String),"owner" .= ("f" :: String),"role" .= (role :: String),"anchor" .= ("signature" :: String)]
      sigDocument = object ["modules" .= [object ["name" .= ("M" :: String)
        ,"sourceCorrespondence" .= object ["occurrences" .= [sigSource "function-signature" "signature",sigSource "function-type" "signature-expression"]]
        ,"sourceAlignment" .= object ["signatures" .= [object ["unavailable" .= Null,"links" .= [sigLink]]]]]]]
      rawSigDef = object ["name" .= ("f" :: String),"type" .= beforeType]
      preparedSigDef ty = object ["name" .= ("f" :: String),"type" .= ty,"preparationOrigin" .= ("f" :: String),"specializationArguments" .= ([] :: [Value])]
      sigOriginal = inv { document = sigDocument, declarations = M.singleton "f" rawSigDef }
      sigPrepared ty = sigOriginal { declarations = M.singleton "f" (preparedSigDef ty) }
      sigDoc = D.mark "f" "calculation" (D.derived "native.calculation" [sigRef] Null []) "calc"
      sigTrace = D.report sigOriginal (sigPrepared afterType) sigDoc
  check (D.validate "calc" sigTrace == Right ()) "validated signature transport rejected"
  check (all ((== String "derived") . get "sourcePrecision") (array (get "targetOccurrences" sigTrace))) "aligned signature did not reach calculation"
  let wrongTrace = D.report sigOriginal (sigPrepared wrongType) sigDoc
  check (all ((== String "unavailable") . get "sourcePrecision") (array (get "targetOccurrences" wrongTrace))) "incorrectly rebased signature was promoted"
  let forgedRoots = case sigTrace of
        Object fs -> Object (KM.insert "checkedRoots" (toJSON [case r of
          Object fields -> Object (KM.insert "value" wrongType fields)
          _ -> r | r <- array (get "checkedRoots" sigTrace)]) fs)
        _ -> Null
  check (isLeft (D.validate "calc" forgedRoots)) "validator accepted a forged signature transport certificate"
  let constructorDocument role = object ["modules" .= [object ["name" .= ("M" :: String)
        ,"sourceCorrespondence" .= object ["occurrences" .= [sigSource role "signature",sigSource "function-type" "signature-expression"]]
        ,"sourceAlignment" .= object ["signatures" .= [object ["unavailable" .= Null,"links" .= [sigLink]]]]]]]
      constructorOriginal role = sigOriginal { document = constructorDocument role }
      constructorTrace role = D.report (constructorOriginal role) (sigPrepared afterType) sigDoc
  check (D.validate "calc" (constructorTrace "constructor-signature") == Right ())
    "explicit constructor signature rejected"
  check (isLeft (D.validate "calc" (constructorTrace "record-constructor")))
    "record constructor name alone masqueraded as a complete signature"
  let otherRef = D.root "other" "type"
      otherDef = object ["name" .= ("other" :: String),"type" .= atom]
      originalWithOther = (constructorOriginal "constructor-signature")
        { declarations = M.insert "other" otherDef (declarations sigOriginal) }
      preparedWithOther = (sigPrepared afterType)
        { declarations = M.insert "other" otherDef (declarations (sigPrepared afterType)) }
      paddingDoc = D.mark "f" "value" (D.derived "native.inactive-payload" [sigRef,otherRef] Null []) "null"
      paddingTrace = D.report originalWithOther preparedWithOther paddingDoc
  check (D.validate "null" paddingTrace == Right ()) "partial schema trace rejected"
  check (all ((== String "unavailable") . get "sourcePrecision") (array (get "targetOccurrences" paddingTrace)))
    "selected constructor signature hid missing inactive-slot schema evidence"
  putStrLn "derivation identity, composition, rendering and malformed-artifact checks passed"
