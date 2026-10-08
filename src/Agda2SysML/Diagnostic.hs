{-# LANGUAGE OverloadedStrings #-}
module Agda2SysML.Diagnostic
  ( Category(..), Refusal, refusal, refuse, category, message, code
  , context, alternatives, causes, field ) where

import qualified Agda2SysML.Derivation as D
import qualified Agda2SysML.Inventory as Inventory
import Data.Aeson (Value, object, (.=))
import Data.Bifunctor (first)
import Data.Text (Text)
import qualified Data.Text as T

data Category = Syntax | Semantics | Representation deriving (Eq,Ord,Show)
data Refusal = Refusal
  { category :: Category, message :: Text, attempts :: [(Text,Refusal)] }
  deriving (Eq,Show)

refusal :: Category -> Text -> Refusal
refusal kind explanation = Refusal kind explanation []

refuse :: Category -> Text -> Either Refusal a
refuse kind = Left . refusal kind

code :: Refusal -> Text
code reason = case category reason of
  Syntax -> "unsupported-syntax"
  Semantics -> "unsupported-semantics"
  Representation -> "unsupported-target-representation"

-- A dependency adds context without reclassifying its underlying failure.
context :: Text -> Refusal -> Refusal
context prefix reason = reason { message = prefix <> message reason }

-- The general algebraic rule is authoritative after the narrower Boolean and
-- homogeneous finite rules fail. Keep every attempt with its own category;
-- one unresolved obligation still produces exactly one diagnostic.
alternatives :: [(Text,Refusal)] -> (Text,Refusal) -> Refusal
alternatives earlier final@(_,primary) = primary
  { message = T.intercalate "; " (map (message . snd) allAttempts)
  , attempts = allAttempts }
  where allAttempts = earlier ++ [final]

causes :: Refusal -> [Value]
causes reason = [object ["rule" .= rule, "code" .= code cause
  ,"message" .= message cause, "causes" .= causes cause] | (rule,cause) <- attempts reason]

-- Inventory/compiler errors retain their existing API. Only their use by a
-- translation rule is classified here as unreadable checked input syntax.
field :: Inventory.Inventory -> Text -> Value -> Either Refusal Value
field inv key definition = fmap decorate (first (refusal Syntax) (Inventory.field inv key definition))
  where decorate = if key `elem` ["type","compiled","projection"]
          then D.annotate (Inventory.string (Inventory.get "name" definition)) key else id
