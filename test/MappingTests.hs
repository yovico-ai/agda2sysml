{-# LANGUAGE OverloadedStrings #-}
module Main (main) where
import Agda2SysML.Mapping
import Control.Monad (unless, forM_)
import qualified Data.ByteString.Char8 as B
import qualified Data.Map.Strict as M
import qualified Data.Text.Encoding as TE
import Data.Either (isLeft, isRight)

base :: B.ByteString
base = B.unlines
  [ "mapping-version: 2"
  , "project: {name: Standalone, agda-library: contract.agda-lib, roots: [Contract]}"
  , "models:"
  , "  contract:"
  , "    module: Contract"
  , "    state: {infer: true}"
  , "    transition:"
  , "      encoding: function"
  , "      symbol: identity"
  , "      arguments: {before: {position: 0}}"
  , "      result: {state: return}"
  ]

replace :: B.ByteString -> B.ByteString -> B.ByteString -> B.ByteString
replace old new = B.intercalate new . split
  where
    split s = let (a,b) = B.breakSubstring old s
      in if B.null b then [a] else a : split (B.drop (B.length old) b)

main :: IO ()
main = do
  accepted <- parseMapping base
  unless (isRight accepted) $ fail (show accepted)
  forM_ invalid $ \(label,input) -> do
    parsed <- parseMapping input
    unless (isLeft parsed) $ fail (label ++ " was accepted: " ++ show parsed)
  -- YAML 1.1's words and dates remain strings under YAML 1.2 core.
  forM_ ["yes","off","2026-03-01"] $ \s -> do
    parsed <- parseMapping (replace "Standalone" s base)
    unless (isRight parsed) $ fail (show parsed)
  forM_ ["true","12","1.5","null","0xFF"] $ \s -> do
    parsed <- parseMapping (replace "Standalone" s base)
    unless (isLeft parsed) $ fail ("non-string name accepted: " ++ show parsed)
  quoted <- parseMapping (replace "symbol: identity" (TE.encodeUtf8 "symbol: '_⟶_'") base)
  case quoted of
    Right m -> unless (length (M.elems (models m)) == 1) $ fail "lost model"
    Left e -> fail e
  putStrLn "mapping reader checks passed"
  where
    invalid =
      [ ("duplicate", "mapping-version: 2\n" <> base)
      , ("unknown key", base <> "extra: value\n")
      , ("version", replace "mapping-version: 2" "mapping-version: 3" base)
      , ("quoted version", replace "mapping-version: 2" "mapping-version: '2'" base)
      , ("multiple documents", base <> "---\n{}\n")
      , ("anchor", replace "Standalone" "&x Standalone" base)
      , ("custom tag", replace "Standalone" "!custom Standalone" base)
      , ("merge key", replace "{infer: true}" "{infer: true, <<: ignored}" base)
      , ("negative selector", replace "position: 0" "position: -1" base)
      , ("floating selector", replace "position: 0" "position: 0.0" base)
      , ("unknown transition field", replace "encoding: function" "encoding: function\n      guard: true" base)
      , ("v2 fields in v1", replace "mapping-version: 2" "mapping-version: 1" base)
      , ("false inference", replace "infer: true" "infer: false" base)
      , ("unpaired command", replace "{before: {position: 0}}" "{before: {position: 0}, command: cmd}" base)
      , ("duplicate roots", replace "roots: [Contract]" "roots: [Contract, Contract]" base)
      ]
