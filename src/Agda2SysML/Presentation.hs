{-# LANGUAGE OverloadedStrings #-}
-- | Source-linked declaration browsing. Documentary elements never discharge
-- a structural or computational obligation; native admission is independent.
module Agda2SysML.Presentation (catalogue, renderCatalogue) where

import Agda2SysML.Inventory
import qualified Agda2SysML.Derivation as D
import Data.Aeson
import qualified Data.ByteString as BS
import Data.List (sortOn, nub)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

catalogue :: Inventory -> [Value] -> [Value]
catalogue inv obligations = [object
  ["symbol" .= symbol,"module" .= get "sourceModule" d,"name" .= get "displayName" d
  ,"kind" .= get "kind" d,"requirements" .= rows
  ,"nativeTargets" .= nub [t | row <- rows,String t <- [get "target" row]]
  ,"documentaryTarget" .= ("AgdaModel::SourceDeclarations::" <> quote owner <> "::" <> quote display)
  ,"contract" .= contract,"source" .= get "source" md
  ,"sourceIntervals" .= [object ["start" .= a,"end" .= b] | (a,b) <- intervals]
  ,"sourceExcerpt" .= excerpt]
  | symbol <- S.toAscList (projectSymbols inv)
  ,Just d <- [M.lookup symbol (declarations inv)]
  ,let owner = string (get "sourceModule" d)
  ,md <- array (get "modules" (document inv)),get "name" md == String owner
  ,let display = string (get "displayName" d)
       rows = [r | r <- obligations,get "symbol" r == String symbol]
       contract = get "kind" d == String "function"
          && any ((== String "proof-source") . get "kind") rows
          && not (any ((== String "behavior") . get "kind") rows)
       raw = sortOn fst [(a,b)
         | occurrence <- array (get "occurrences" (get "sourceCorrespondence" md))
         ,get "owner" occurrence == String symbol
         ,get "role" occurrence `elem` map String
           ["function-signature","function","constructor-signature","datatype-signature"
           ,"datatype","record-signature","record","field-signature","type-signature","primitive-signature"]
         ,spanValue <- array (get "intervals" occurrence)
         ,Just a <- [integer (get "start" spanValue)],Just b <- [integer (get "end" spanValue)]]
       intervals = foldr merge [] raw
       bytes = TE.encodeUtf8 (string (get "sourceText" md))
       excerpt = T.intercalate "\n" [TE.decodeUtf8 (BS.take (b-a) (BS.drop a bytes)) | (a,b) <- intervals]]
  where
    merge (a,b) ((c,e):rest) | b >= c = merge (a,max b e) rest
    merge interval rest = interval:rest
    integer (Number n) = toBoundedInteger n
    integer _ = Nothing

quote :: Text -> Text
quote = (<> "'") . ("'" <>) . T.replace "'" "\\'" . T.replace "\\" "\\\\"

renderCatalogue :: [Value] -> D.Doc
renderCatalogue [] = ""
renderCatalogue entries = "  package SourceDeclarations {\n" <> mconcat
  [D.text ("    package " <> quote owner <> " {\n")
    <> mconcat [entry item | item <- entries,get "module" item == String owner]
    <> "    }\n" | owner <- S.toAscList (S.fromList (map (string . get "module") entries))]
  <> "  }\n"
  where
    entry item = D.boundary (string (get "symbol" item)) "source.declaration-documentation"
      ["      " <> (if get "contract" item == Bool True then "requirement def " else "package ")
          <> quote (string (get "name" item)) <> " {"
      ,"        doc /* " <> escape (documentation item) <> " */"
      ,"      }"]
    escape = T.replace "*/" "* /"
    documentation item = T.intercalate "\n"
      ["Retained Agda " <> string (get "kind" item) <> "; documentary source, not executable translation evidence."
      ,"Checked declaration: " <> string (get "symbol" item)
      ,"Source: " <> string (get "library" (get "source" item)) <> ":" <> string (get "path" (get "source" item))
      ,"Native targets: " <> T.intercalate ", " (map string (array (get "nativeTargets" item)))
      ,"Requirements: " <> T.intercalate "; " [string (get "kind" r) <> " " <> string (get "status" r)
          <> maybeText (get "reason" r) | r <- array (get "requirements" item)]
      ,if T.null (string (get "sourceExcerpt" item)) then
          "No direct declaration anchor; the complete checked signature is in inventory.json."
          else string (get "sourceExcerpt" item)]
    maybeText (String reason) = " (" <> reason <> ")"
    maybeText _ = ""
