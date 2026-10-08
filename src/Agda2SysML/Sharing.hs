{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Agda2SysML.Sharing (Nodes, emptyNodes, compactRecord, intern, internWith, internShallow, expand, digest) where

import Control.Monad.State.Strict
import Control.Monad (when)
import Crypto.Hash.SHA256 (hash)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Char (intToDigit)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

type Nodes = M.Map Text Value
emptyNodes :: Nodes
emptyNodes = M.empty

digest :: BS.ByteString -> Text
digest = T.pack . concatMap (\b -> [intToDigit (fromIntegral b `div` 16),intToDigit (fromIntegral b `mod` 16)]) . BS.unpack . hash

compactRecord :: Value -> State Nodes Value
compactRecord (Object fields) = Object <$> traverse intern fields
compactRecord value = intern value

intern :: Value -> State Nodes Value
intern = internWith digest

-- Child references are installed first, hence every produced graph is acyclic.
-- Exact equality is checked even after a hash match. A collision is assigned a
-- distinct deterministic suffix and cannot identify unequal values.
internWith :: (BS.ByteString -> Text) -> Value -> State Nodes Value
internWith fingerprint value = case value of
  Object fields -> traverse recurse fields >>= saveWith fingerprint . object . pure . ("object" .=)
  Array xs -> traverse recurse xs >>= saveWith fingerprint . object . pure . ("array" .=)
  scalar -> pure scalar
  where
    recurse = internWith fingerprint

-- Children have already been packed by the typed compiler serializer. Unlike
-- 'intern', this does not interpret an existing child reference as source data.
internShallow :: Value -> State Nodes Value
internShallow (Object fields) = saveWith digest (object ["object" .= Object fields])
internShallow (Array values) = saveWith digest (object ["array" .= Array values])
internShallow scalar = pure scalar

saveWith :: (BS.ByteString -> Text) -> Value -> State Nodes Value
saveWith fingerprint payload = do
      table <- get
      let base = fingerprint (BL.toStrict (encode payload))
          choose n = let candidate = base <> if n == (0 :: Int) then "" else ":" <> T.pack (show n)
            in case M.lookup candidate table of
              Nothing -> candidate
              Just existing | existing == payload -> candidate
              _ -> choose (n + 1)
          key = choose 0
      modify' (M.insert key payload)
      pure (object ["$node" .= key])

-- The reader rejects missing references, malformed entries, and cycles. It is
-- memoized: reconstruction shares Haskell values instead of copying subtrees.
expand :: Nodes -> Value -> Either String Value
expand table value = evalStateT (walk S.empty value) M.empty
  where
    walk active (Object fields) | Just (String key) <- KM.lookup "$node" fields, KM.size fields == 1 = do
      memo <- get
      case M.lookup key memo of
        Just cached -> pure cached
        Nothing -> do
          when (S.member key active) $ lift (Left "cyclic shared term")
          payload <- maybe (lift $ Left "missing shared term") pure (M.lookup key table)
          result <- case payload of
            Object p | KM.size p == 1 -> case (KM.lookup "object" p,KM.lookup "array" p) of
              (Just (Object fs),Nothing) -> Object <$> traverse (walk (S.insert key active)) fs
              (Nothing,Just (Array xs)) -> Array <$> traverse (walk (S.insert key active)) xs
              _ -> lift (Left "malformed shared term")
            _ -> lift (Left "malformed shared term")
          modify' (M.insert key result)
          pure result
    walk active (Object fields) = Object <$> traverse (walk active) fields
    walk active (Array xs) = Array <$> traverse (walk active) xs
    walk _ scalar = pure scalar
