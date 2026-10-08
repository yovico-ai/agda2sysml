{-# LANGUAGE OverloadedStrings #-}
module Main where

import Agda2SysML.Source (sourceInfo)
import Agda2SysML.SourceCatalog
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (emptyScopeInfo)
import Agda.TypeChecking.Monad.Base (runTCMTop)
import Agda.Utils.FileName (absolute)
import Control.Monad (unless, forM_)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString as BS
import Data.Foldable (toList)
import Data.Either (isLeft)
import Data.List (nub)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

get :: Key -> Value -> Value
get k (Object fs) = maybe Null id (KM.lookup k fs)
get _ _ = Null
array :: Value -> [Value]
array (Array xs) = toList xs
array _ = []
number :: Value -> Int
number (Number n) = round n
number _ = error "expected offset"
pick :: [a] -> a
pick (x:_) = x
pick [] = error "missing expected fixture occurrence"

check :: Bool -> String -> IO ()
check ok message = unless ok (fail message)

parse :: Text -> IO Value
parse contents = do
  path <- absolute "/tmp/Catalog.agda"
  result <- runTCMTop (sourceInfo emptyScopeInfo (mkRangeFile path Nothing) (T.unpack contents))
  case result of
    Left err -> fail ("source parser rejected catalog fixture: " ++ show err)
    Right (_,nodes) -> pure (catalog "Catalog" contents nodes)

slice :: Text -> Value -> [Text]
slice text occurrence = [TE.decodeUtf8 (BS.take (end-start) (BS.drop start (TE.encodeUtf8 text)))
  | i <- array (get "intervals" occurrence),let start = number (get "start" i),let end = number (get "end" i)]

main :: IO ()
main = do
  let contents = T.unlines
        ["module Catalog where", "data Choice : Set where", "  yes no : Choice"
        ,"record Pair : Set where", "  constructor pair", "  field left right : Choice"
        ,"identity : Choice → Choice", "identity x = x"
        ,"repeat : Choice → Choice", "repeat yes = identity yes", "repeat no = identity yes"
        ,"select : Choice → Choice", "select x with identity x", "... | yes = yes", "... | no = no"
        ,"dependent : (A : Set) → A → A", "dependent A x = x"
        ,"unicode : Choice → Choice", "unicode α = identity α"]
  base <- parse contents
  shifted <- parse ("\n\n" <> contents)
  crlf <- parse (T.replace "\n" "\r\n" contents)
  let occurrences = array (get "occurrences" base)
      shiftedItems = array (get "occurrences" shifted)
      ids = map (get "id") occurrences
      repeated = [o | o <- occurrences, get "role" o == String "raw-application", T.unwords (concatMap T.words (slice contents o)) == "identity yes"]
  check (length ids == length (nub ids) && not (null ids)) "structural occurrence IDs collide"
  check (map (get "id") shiftedItems == ids) "line movement changed occurrence identity"
  check (map (get "id") (array (get "occurrences" crlf)) == ids) "newline convention changed syntax identity"
  check (get "checkedTextDigest" base /= get "checkedTextDigest" shifted) "catalog has stale checked text digest"
  check (length repeated == 2 && get "id" (pick repeated) /= get "id" (pick (reverse repeated))) "identical RHS occurrences collapsed"
  forM_ [(contents,occurrences),("\n\n" <> contents,shiftedItems),(T.replace "\n" "\r\n" contents,array (get "occurrences" crlf))] $ \(text,items) ->
    forM_ items $ \o -> do
      check (get "rangeUnavailable" o /= String "invalid-source-range") ("invalid Unicode/tab/newline position: " ++ show o)
      check (get "parent" o == Null || get "parent" o `elem` map (get "id") items) "parent occurrence is missing"
      forM_ (array (get "intervals" o)) $ \i -> do
        let a = number (get "start" i); b = number (get "end" i)
        check (0 <= a && a < b && b <= BS.length (TE.encodeUtf8 text)) "source interval escapes checked text"
  check (any ((== ["α"]) . slice contents) occurrences) "Unicode identifier byte slice is wrong"
  forM_ ["constructor-signature","record","field-signature","typed-binding","with-clauses"] $ \role ->
    check (any ((== String role) . get "role") occurrences) ("missing syntax role " ++ T.unpack role)
  let missing = catalog "M" "" [SyntaxNode "rhs" noRange Nothing Nothing []]
  check (all ((== String "source-range-unavailable") . get "rangeUnavailable") (array (get "occurrences" missing))) "missing ranges became exact empty spans"
  -- Explicitly exercise disjoint intervals independently of syntax grouping.
  let p0 = startPos Nothing
      p1 = movePos p0 'a'
      p2 = movePos p1 ' '
      p3 = movePos p2 'b'
      multi = catalog "M" "a b" [SyntaxNode "parts"
        (Range (srcFile p0) (Seq.fromList
          [Interval () (fmap (const ()) p0) (fmap (const ()) p1)
          ,Interval () (fmap (const ()) p2) (fmap (const ()) p3)])) Nothing Nothing []]
  check (map (slice "a b") (array (get "occurrences" multi)) == [["a","b"]]) "disjoint ranges became an envelope"
  let tab = movePos p0 '\t'
      alpha = movePos tab 'α'
      tabbed = catalog "M" "\tα" [SyntaxNode "identifier"
        (Range (srcFile p0) (Seq.singleton (Interval () (fmap (const ()) tab) (fmap (const ()) alpha)))) Nothing Nothing []]
  check (map (slice "\tα") (array (get "occurrences" tabbed)) == [["α"]]) "tab/Unicode cursor conversion is wrong"
  let anchor = pick [o | o <- occurrences,get "binding" o /= Null,get "role" o == String "function-signature"]
      definition name = object ["name" .= (name :: Text),"bindingModule" .= ("Catalog" :: Text),"source" .= get "binding" anchor]
      bundle :: [Value] -> Value
      bundle defs = object ["nodes" .= object [],"modules" .= [object ["name" .= ("Catalog" :: Text)
        ,"definitions" .= defs,"sourceCorrespondence" .= base]]]
      annotated defs = either (error . T.unpack) (get "sourceCorrespondence" . pick . array . get "modules") (attachOwners (bundle defs))
      ownerAt cat = pick [o | o <- array (get "occurrences" cat), get "id" o == get "id" anchor]
  check (get "owner" (ownerAt (annotated [definition "f"])) == String "f") "unique checked binding not attached"
  check (get "ownerUnavailable" (ownerAt (annotated [])) == String "source-anchor-unavailable") "missing checked owner guessed"
  check (get "ownerUnavailable" (ownerAt (annotated [definition "f",definition "g"])) == String "source-anchor-ambiguous") "ambiguous checked owner guessed"
  check (map (get "id") (array (get "occurrences" (annotated [definition "f"]))) == ids) "ownership changed occurrence IDs"
  let set k v (Object fs) = Object (KM.insert k v fs)
      set _ _ v = v
      child = toJSON [String "constructors",Number 0,String "branch",String "tree"]
      leafTree = object ["tag" .= ("done" :: Text),"binders" .= [Null,Null]]
      tree = object ["tag" .= ("case" :: Text),"argument" .= object ["value" .= (1 :: Int)]
        ,"constructors" .= [object ["symbol" .= ("C#canonical" :: Text)
          ,"branch" .= object ["arity" .= (2 :: Int),"tree" .= leafTree]]]]
      split = object ["path" .= ([] :: [Value]),"argument" .= (1 :: Int)
        ,"constructor" .= ("C#canonical" :: Text),"arity" .= (2 :: Int),"branch" .= (0 :: Int),"child" .= child]
      certificate = object ["leaf" .= child,"splits" .= [split],"binderPermutation" .= [1,0 :: Int]]
      link = object ["checked" .= object ["root" .= ("compiled" :: Text),"path" .= ([] :: [Value])]
        ,"source" .= ("clause" :: Text),"clause" .= ("clause" :: Text),"replay" .= certificate]
      changedSplit k v = set "replay" (set "splits" (toJSON [set k v split]) certificate) link
  check (validateClauseReplay tree link == Right ()) "valid case replay rejected"
  let contextLink = set "rule" "source.compiled-clause" link
  check (validateClauseCoverage tree (toJSON ([] :: [Value])) [contextLink] == Right ()) "complete case coverage rejected"
  check (isLeft (validateClauseCoverage tree (toJSON ([] :: [Value])) [])) "missing case evidence accepted"
  check (isLeft (validateClauseCoverage tree (toJSON ([] :: [Value])) [contextLink,contextLink])) "duplicate case evidence accepted"
  let twoBranches = set "constructors" (toJSON (array (get "constructors" tree) ++ array (get "constructors" tree))) tree
  check (isLeft (validateClauseCoverage twoBranches (toJSON ([] :: [Value])) [contextLink])) "one branch promoted an entire case"
  forM_ [changedSplit "constructor" "C#different",changedSplit "argument" (Number 0)
    ,changedSplit "arity" (Number 1),changedSplit "branch" (Number 1),changedSplit "child" (toJSON ([] :: [Value]))
    ,set "replay" (set "binderPermutation" (toJSON [0,0 :: Int]) certificate) link
    ,set "checked" (object ["root" .= ("compiled" :: Text),"path" .= [String "body"]]) link
    ,set "source" "rhs" link] $ \bad ->
      check (isLeft (validateClauseReplay tree bad)) "malformed case replay accepted"
  putStrLn "source occurrence, ownership, coordinate, and clause replay checks passed"
