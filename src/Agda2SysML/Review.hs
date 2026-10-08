{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}
module Agda2SysML.Review (render) where

import Agda2SysML.Inventory
import qualified Agda2SysML.Presentation as Presentation
import qualified Agda2SysML.Target as Target
import Data.Aeson
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Language.Haskell.TH (stringE)
import Language.Haskell.TH.Syntax (addDependentFile, runIO)

-- Compile the viewer into the executable; opening a bundle requires no server,
-- network access, runtime assets or installation-dependent paths.
template :: T.Text
template = T.pack $(do
  addDependentFile "assets/review.html"
  runIO (readFile "assets/review.html") >>= stringE)

render :: Inventory -> Target.Generated -> T.Text
render inv generated = T.replace "@@PAYLOAD@@" safe template
  where
    report = Target.correspondence generated
    rows = array (get "obligations" report)
    entries = filter (not . null . array . get "requirements") (Presentation.catalogue inv rows)
    trace = get "sourceCorrespondence" report
    derivations = M.fromList [(get "id" d,d) | d <- array (get "derivations" trace)]
    bytes = TE.encodeUtf8 (Target.modelText generated)
    fragments symbol = [TE.decodeUtf8 (BS.take (b-a) (BS.drop a bytes))
      | target <- array (get "targetOccurrences" trace),get "owner" target == String symbol
      ,Just derivation <- [M.lookup (get "derivation" target) derivations]
      ,"native." `T.isPrefixOf` string (get "rule" (get "evidence" derivation))
      ,get "role" target `elem` [String "calculation",String "boundary"]
      ,spanValue <- array (get "intervals" target)
      ,Just a <- [integer (get "start" spanValue)],Just b <- [integer (get "end" spanValue)]]
    dataValue = object ["project" .= get "project" (document inv),"complete" .= Target.complete generated
      ,"coverage" .= get "coverage" report,"validated" .= True
      ,"declarations" .= [object ["declaration" .= entry,"nativeText" .= fragments (string (get "symbol" entry))] | entry <- entries]]
    -- JSON stays data even if a source comment contains HTML/script delimiters.
    safe = T.replace "<" "\\u003c" $ T.replace "&" "\\u0026" $ TE.decodeUtf8 (BL.toStrict (encode dataValue))
    integer (Number n) = toBoundedInteger n
    integer _ = Nothing
