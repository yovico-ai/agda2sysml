{-# LANGUAGE OverloadedStrings #-}
-- | Dependency accounting over the checked inventory. Discovery never expands
-- whole term trees: only the requested shared field is reconstructed.
module Agda2SysML.Inventory
  ( Inventory(..), prepare, field, array, string, get, required, sourceManifest, assumptions, enclosures, terminationChecked, inductiveChecked, projectSymbols ) where

import qualified Agda2SysML.Mapping as C
import qualified Agda2SysML.Sharing as Sharing
import Control.Monad (unless, forM_)
import Data.Aeson
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Foldable (toList)
import Data.List (inits)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

data Inventory = Inventory
  { document :: Value
  , declarations :: M.Map Text Value
  , nodes :: Sharing.Nodes
  , modelRequirements :: M.Map Text (S.Set (Text, Text))
  }

get :: Text -> Value -> Value
get k (Object o) = fromMaybe Null (KM.lookup (K.fromText k) o)
get _ _ = Null
array :: Value -> [Value]
array (Array a) = toList a
array _ = []
string :: Value -> Text
string (String s) = s
string _ = ""

field :: Inventory -> Text -> Value -> Either Text Value
field inv k v = either (Left . T.pack) Right $ Sharing.expand (nodes inv) (get k v)

prepare :: C.Mapping -> Value -> Either Text Inventory
prepare mapping input = do
  let defs = concatMap (array . get "definitions") (array (get "modules" input))
      grouped = M.fromListWith (++) [(string (get "name" d),[d]) | d <- defs]
      table = case get "nodes" input of
        Object fields -> M.fromList [(K.toText k,v) | (k,v) <- KM.toList fields]
        _ -> M.empty
  forM_ (M.toList grouped) $ \(key,ds) ->
    unless (not (T.null key) && length ds == 1) (Left ("canonical-identity-conflict: " <> key))
  let inv = Inventory input (M.fromList [(key,d) | (key,[d]) <- M.toList grouped]) table M.empty
  -- Check edges even outside the required scope; omitted support is an inventory
  -- error, not an opportunity to shrink the semantic dependency closure.
  forM_ defs $ \d -> do
    deps <- dependencies inv d
    forM_ deps $ \dep -> unless (M.member dep (declarations inv)) $
      Left ("missing-dependency: " <> string (get "name" d) <> " -> " <> dep)
  annotations <- M.traverseWithKey (requirementsFor inv) (C.models mapping)
  requirements <- if get "selectionProfile" input == String "declarations" then do
    seeds <- fmap concat $ traverse (defaultRoles inv) (S.toAscList (projectSymbols inv))
    selected <- requirementClosure inv seeds
    pure (M.insert "$declarations" selected annotations)
    else pure annotations
  pure inv { modelRequirements = requirements }

-- Checked library ownership, rather than a source-module spelling convention,
-- determines the default scope. Imported dependencies enter through closure.
projectSymbols :: Inventory -> S.Set Text
projectSymbols inv = S.fromList [string (get "name" d)
  | String libraryName <- [get "library" (document inv)],not (T.null libraryName)
  ,md <- array (get "modules" (document inv))
  ,get "library" (get "source" md) == get "library" (document inv)
  ,d <- array (get "definitions" md)]

defaultRoles :: Inventory -> Text -> Either Text [(Text,Text)]
defaultRoles inv symbol = do
  d <- maybe (Left "missing project declaration") Right (M.lookup symbol (declarations inv))
  let retained = [(symbol,"statement"),(symbol,"proof-source")]
  case string (get "kind" d) of
    "function" -> do
      ty <- field inv "type" d
      let terminal t | get "tag" (get "term" t) == String "pi" = terminal (get "body" (get "codomain" (get "term" t)))
                     | otherwise = get "term" t
          result = terminal ty
          equality = get "equality" (get "builtins" (document inv))
      pure $ if equality /= Null && get "tag" result == String "definition" && get "symbol" result == equality
        then retained else [(symbol,"behavior")]
    "primitive" -> pure [(symbol,"behavior")]
    "axiom" -> do
      ty <- field inv "type" d
      let role = if get "tag" (get "term" ty) == String "sort" then "structure" else "behavior"
      pure [(symbol,"statement"),(symbol,"external-assumption"),(symbol,role)]
    _ -> pure [(symbol,"structure")]

dependencies :: Inventory -> Value -> Either Text [Text]
dependencies inv d = do
  statement <- field inv "statementDependencies" d
  body <- field inv "bodyDependencies" d
  constructors <- field inv "constructors" d
  fields <- field inv "fields" d
  constructor <- field inv "constructor" d
  pure (map string (array statement ++ array body ++ array constructors ++ array fields)
    ++ [s | String s <- [constructor]])

required :: Inventory -> S.Set (Text,Text)
required = S.unions . M.elems . modelRequirements

-- Safe modules forbid TERMINATING/NON_TERMINATING pragmas. A positive
-- function flag without that module evidence is not a checked certificate.
terminationChecked :: Inventory -> Value -> Bool
terminationChecked inv d = get "terminates" d == Bool True && any checked (array (get "checking" (document inv)))
  where
    owner = if get "sourceModule" d == Null then get "module" d else get "sourceModule" d
    checked m = get "module" m == owner && get "safe" m == Bool True && get "terminationCheck" m == Bool True

inductiveChecked :: Inventory -> Value -> Bool
inductiveChecked inv d = get "kind" d == String "datatype" && get "induction" d == String "Inductive"
  && any checked (array (get "checking" (document inv)))
  where
    owner = if get "sourceModule" d == Null then get "module" d else get "sourceModule" d
    checked m = get "module" m == owner && get "safe" m == Bool True && get "positivityCheck" m == Bool True

requirementsFor :: Inventory -> Text -> C.Model -> Either Text (S.Set (Text,Text))
requirementsFor inv modelId model = do
  resolution <- case filter ((== modelId) . string . get "model") (array (get "resolutions" (document inv))) of
    [r] -> Right r
    _ -> Left ("missing-model-resolution: " <> modelId)
  let refs = M.fromList [(string (get "reference" r), map string (array (get "candidates" r)))
                       | r <- array (get "references" resolution)]
      resolve r = case M.lookup r refs of
        Just [symbol] -> Right symbol
        _ -> Left ("invalid-resolved-reference: " <> r)
      seed r role = (\s -> (s,role)) <$> resolve r
      mainSeeds = case C.transition model of
        C.Function s _ _ result -> seed s "behavior" : case result of
          C.DirectState -> []
          C.Family family projection _ -> [seed family "structure", seed projection "behavior"]
        C.Relation s _ _ -> [seed s "behavior"]
      structureSeeds = [seed s "structure" | C.NamedState s <- [C.state model]]
        ++ maybe [] (\s -> [seed s "structure"]) (C.commands model)
      contractSeeds = [seed s "behavior" | C.Invariant s _ <- C.invariants model]
        ++ concat [[seed s "statement",seed s "proof-source"] | s <- C.theorems model]
  seeds <- sequence (mainSeeds ++ structureSeeds ++ contractSeeds)
  requirementClosure inv seeds

requirementClosure :: Inventory -> [(Text,Text)] -> Either Text (S.Set (Text,Text))
requirementClosure inv = closure S.empty
  where
    closure seen [] = Right seen
    closure seen (item@(symbol,role):rest)
      | S.member item seen = closure seen rest
      | otherwise = do
          d <- maybe (Left ("missing-required-declaration: " <> symbol)) Right (M.lookup symbol (declarations inv))
          statement <- map string . array <$> field inv "statementDependencies" d
          body <- map string . array <$> field inv "bodyDependencies" d
          constructors <- map string . array <$> field inv "constructors" d
          recordConstructor <- field inv "constructor" d
          fields <- map string . array <$> field inv "fields" d
          let dependencyRole s = case M.lookup s (declarations inv) of
                Just def | get "kind" def `elem` [String "function",String "primitive"] -> "behavior"
                _ -> "structure"
              statementNeeds = [(s,if role == "statement" then "statement" else dependencyRole s) | s <- statement]
              structural = [(s,if role == "statement" then "statement" else "structure")
                | s <- constructors ++ fields ++ [c | String c <- [recordConstructor]]]
              bodyNeeds = case role of
                "proof-source" -> [(s,"proof-source") | s <- body]
                "statement" -> []
                _ -> [(s,dependencyRole s) | s <- body]
              -- Proof-source retention follows proof dependencies without
              -- pretending their executable bodies have been translated.
              more = (if role == "proof-source" then [] else statementNeeds ++ structural) ++ bodyNeeds
          closure (S.insert item seen) (more ++ rest)

sourceManifest :: Inventory -> [Value]
sourceManifest inv = [object
  ["module" .= get "name" md, "source" .= get "source" md
  ,"checkedTextDigest" .= Sharing.digest (TE.encodeUtf8 (string (get "sourceText" md)))]
  | md <- array (get "modules" (document inv))]

-- Qualify claims by the complete dependency graph, including proof bodies.
-- An axiom remains explicit even when a builtin module is allowed to declare
-- it under safe mode. This report does not equate safe checking with absence
-- of a trusted foundation.
assumptions :: Inventory -> Either Text Value
assumptions inv = do
  edges <- traverse (dependencies inv) (declarations inv)
  let reachable seen [] = seen
      reachable seen (s:rest)
        | S.member s seen = reachable seen rest
        | otherwise = reachable (S.insert s seen) (M.findWithDefault [] s edges ++ rest)
      qualify needs = let
        closure = reachable S.empty (map fst (S.toList needs))
        defs = [d | s <- S.toAscList closure, Just d <- [M.lookup s (declarations inv)]]
        sourceModules = S.fromList (map (string . get "sourceModule") defs)
        checks = [c | c <- array (get "checking" (document inv)), S.member (string (get "module" c)) sourceModules]
        in object ["axioms" .= [get "id" d | d <- defs, get "kind" d == String "axiom"]
          ,"checking" .= checks, "dependencyCount" .= S.size closure]
  pure (toJSON (M.map qualify (modelRequirements inv)))

-- Namespace identities establish ownership even when several local modules
-- print as the same underscore. A spelling or shared source line is insufficient.
enclosures :: Inventory -> Either Text Value
enclosures inv = do
  whereModules <- traverse (field inv "whereModules") (declarations inv)
  let owners = M.fromListWith (++) [(map string (array namespace),[symbol])
        | (symbol,spaces) <- M.toAscList whereModules, namespace <- array spaces]
  paths <- traverse (field inv "moduleIdentity") (declarations inv)
  pure $ toJSON $ M.mapMaybeWithKey (\symbol path ->
    let enclosing = filter (/= symbol) $ concatMap (\p -> M.findWithDefault [] p owners) (inits (map string (array path)))
    in if null enclosing then Nothing else Just enclosing) paths
