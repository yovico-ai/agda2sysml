{-# LANGUAGE OverloadedStrings #-}
-- | Combine checked roots without retaining duplicate import closures. A shared
-- source or compiler node cannot silently change halfway through an invocation.
module Agda2SysML.Merge (mergeRoots) where

import Control.Monad (foldM, unless)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Foldable (toList)
import qualified Data.Map.Strict as M
import Data.Text (Text)

get :: Key -> Value -> Value
get key (Object objectFields) = maybe Null id (KM.lookup key objectFields)
get _ _ = Null

array :: Value -> [Value]
array (Array xs) = toList xs
array _ = []

fields :: Value -> KM.KeyMap Value
fields (Object xs) = xs
fields _ = KM.empty

mergeRoots :: Value -> Value -> Either Text Value
mergeRoots Null incoming = Right incoming
mergeRoots previous incoming = do
  nodes <- combine False "shared-node identity conflict" (get "nodes" previous) (get "nodes" incoming)
  builtins <- combine True "builtin identity conflict" (get "builtins" previous) (get "builtins" incoming)
  modules <- byKey "name" mergeModule (get "modules" previous) (get "modules" incoming)
  checks <- byKey "module" (equal "checking options changed between roots") (get "checking" previous) (get "checking" incoming)
  resolutions <- byKey "model" mergeResolution (get "resolutions" previous) (get "resolutions" incoming)
  pure $ object ["schemaVersion" .= (1 :: Int), "modules" .= modules, "nodes" .= nodes
    ,"builtins" .= builtins, "checking" .= checks, "resolutions" .= resolutions]
  where
    combine optional message a b = Object <$> foldM (\acc (key,value) -> case KM.lookup key acc of
      Nothing -> Right (KM.insert key value acc)
      Just Null | optional -> Right (KM.insert key value acc)
      Just old | (optional && value == Null) || value == old -> Right acc
               | otherwise -> Left message) (fields a) (KM.toList (fields b))
    equal message a b = if a == b then Right a else Left message
    byKey key merge a b = do
      result <- foldM (\acc entry -> case M.lookup (get key entry) acc of
        Nothing -> Right (M.insert (get key entry) entry acc)
        Just old -> do merged <- merge old entry; Right (M.insert (get key entry) merged acc))
        M.empty (array a ++ array b)
      pure (toJSON (M.elems result))
    mergeResolution a b
      | get "outsideScope" a == Bool True = Right b
      | get "outsideScope" b == Bool True = Right a
      | otherwise = equal "mapping resolution changed between roots" a b
    mergeModule a b = do
      unless (KM.delete "definitions" (fields a) == KM.delete "definitions" (fields b)) $
        Left "checked source module changed between roots"
      definitions <- byKey "name" mergeDefinition (get "definitions" a) (get "definitions" b)
      pure (Object (KM.insert "definitions" definitions (fields a)))
    mergeDefinition a b = do
      -- A helper found only in an imported signature may subsequently be visited
      -- as a normal declaration. Only its origin annotation may differ.
      let semantic objectFields = foldr KM.delete objectFields ["sourceSyntax", "generatedSupport", "origin"]
      unless (semantic (fields a) == semantic (fields b)) $
        Left "checked declaration changed between roots"
      if get "generatedSupport" a == Bool True then Right b
      else if get "generatedSupport" b == Bool True then Right a
      else equal "declaration source origin changed between roots" a b
