{-# LANGUAGE OverloadedStrings #-}
module Main where

import Agda2SysML.Merge
import Control.Monad (unless)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Either (isLeft)

main :: IO ()
main = do
  let definition generated = object (["name" .= ("f" :: String), "type" .= ("T" :: String)] ++
        ["generatedSupport" .= True | generated])
      root source definitions nodes resolution = object
        ["schemaVersion" .= (1 :: Int), "builtins" .= object []
        ,"modules" .= [object ["name" .= ("M" :: String), "sourceText" .= source, "definitions" .= definitions]]
        ,"nodes" .= nodes, "resolutions" .= [resolution], "checking" .= ([] :: [Value])]
      unresolved = object ["model" .= ("m" :: String), "outsideScope" .= True]
      resolved = object ["model" .= ("m" :: String), "references" .= ([] :: [Value])]
      a = root ("source" :: String) [definition True] (object ["key" .= ("value" :: String)]) unresolved
      b = root ("source" :: String) [definition False] (object ["key" .= ("value" :: String)]) resolved
      check x = unless x (fail "checked-root merge regression")
  check (mergeRoots a a == Right a)
  check (mergeRoots a b == Right b)
  check (mergeRoots b a == Right b)
  check (isLeft (mergeRoots a (root ("changed" :: String) [definition True] (object []) unresolved)))
  check (isLeft (mergeRoots a (root ("source" :: String) [definition True] (object ["key" .= False]) unresolved)))
  check (isLeft (mergeRoots a (root ("source" :: String)
    [object ["name" .= ("f" :: String), "type" .= ("Other" :: String)]] (object []) unresolved)))
  let replace key value (Object fields) = Object (KM.insert key value fields)
      replace _ _ v = v
  check (isLeft (mergeRoots (replace "checking" (toJSON [object ["module" .= ("M" :: String), "safe" .= True]]) a)
    (replace "checking" (toJSON [object ["module" .= ("M" :: String), "safe" .= False]]) b)))
  putStrLn "checked-root consistency checks passed"
