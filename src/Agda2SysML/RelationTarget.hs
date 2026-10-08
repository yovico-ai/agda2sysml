{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Agda2SysML.RelationTarget (Relation(..), Rule(..), Term(Witness, BooleanValue, EnumValue), relation, render, renderDoc) where

import qualified Agda2SysML.Derivation as D
import Agda2SysML.Inventory hiding (field)
import Agda2SysML.Diagnostic
import qualified Agda2SysML.FiniteTarget as F
import Control.Monad (unless)
import Data.Aeson
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)
import qualified Data.Text as T

data Type = Boolean | Enumeration F.Domain deriving (Eq, Show)
data Term = Annotated D.Origin Term
  | NWitness Int
  | NBooleanValue Bool
  | NEnumValue F.Domain Text
  deriving Show

unmark :: Term -> Term
unmark (Annotated _ x) = unmark x
unmark x = x

instance Eq Term where
  x == y | NWitness a0 <- unmark x, NWitness b0 <- unmark y = a0 == b0
  x == y | NBooleanValue a0 <- unmark x, NBooleanValue b0 <- unmark y = a0 == b0
  x == y | NEnumValue a0 a1 <- unmark x, NEnumValue b0 b1 <- unmark y = a0 == b0 && a1 == b1
  _ == _ = False
pattern Witness :: Int -> Term
pattern Witness i <- (unmark -> NWitness i) where Witness i = NWitness i
pattern BooleanValue :: Bool -> Term
pattern BooleanValue b <- (unmark -> NBooleanValue b) where BooleanValue b = NBooleanValue b
pattern EnumValue :: F.Domain -> Text -> Term
pattern EnumValue s c <- (unmark -> NEnumValue s c) where EnumValue s c = NEnumValue s c
{-# COMPLETE Witness, BooleanValue, EnumValue #-}

annotation :: Term -> D.Origin
annotation (Annotated o _) = o
annotation _ = D.generated "native.generated-expression"

located :: Text -> Value -> Value -> Term -> Term
-- A fresh root gets its first justified origin here. Existing annotations,
-- including explicit unavailable boundaries, must survive unchanged as premises.
located rule input premises e = Annotated (D.origin rule input premises parents) e
  where parents = case e of Annotated o _ -> [o]; _ -> []

data Rule = Rule { ruleSymbol :: Text, witnesses :: [Type], endpoints :: [Term] } deriving (Eq, Show)
data Relation = Relation { relationSymbol :: Text, indices :: [Type], rules :: [Rule] } deriving (Eq, Show)

relation :: Inventory -> M.Map Text F.Domain -> Value -> Either Refusal Relation
relation inv domains def = do
  unless (get "kind" def == String "datatype" && get "abstract" def == Bool False) $
    refuse Representation "The finite relation rule requires a concrete indexed datatype"
  parameters <- field inv "parameters" def
  unless (parameters == Number 0) (refuse Representation "Parameterized relations need a domain-family rule")
  ty <- field inv "type" def
  (inputTypes,_,result) <- telescope ty
  unless (not (null inputTypes) && get "tag" (get "term" result) == String "sort") $
    refuse Representation "The finite relation rule requires indices and a proposition result"
  indexTypes <- traverse typ inputTypes
  cs <- map string . array <$> field inv "constructors" def
  constructors <- traverse (constructor indexTypes) cs
  pure (Relation symbol indexTypes constructors)
  where
    symbol = string (get "name" def)
    builtin key = string (get key (get "builtins" (document inv)))
    typ ty = let t = get "term" ty; s = string (get "symbol" t) in do
      unless (get "tag" t == String "definition" && get "eliminations" t == toJSON ([] :: [Value])) $
        refuse Representation "Dependent witnesses and indices need another relation rule"
      if s == builtin "bool" && not (T.null s) then Right Boolean
      else maybe (refuse Representation "Witness or index type has no finite carrier") (Right . Enumeration) (M.lookup s domains)
    constructor indexTypes c = do
      d <- maybe (refuse Syntax "Missing relation constructor") Right (M.lookup c (declarations inv))
      ty <- field inv "type" d
      (arguments,bindings,result) <- telescope ty
      args <- traverse typ arguments
      let t = get "term" result
      unless (get "tag" t == String "definition" && get "symbol" t == String symbol) $
        refuse Semantics "Constructor result is not the selected relation"
      values <- traverse application (array (get "eliminations" t))
      unless (length values == length indexTypes) (refuse Syntax "Constructor has an inconsistent index count")
      expressions <- sequence [term args bindings indexType value | (indexType,value) <- zip indexTypes values]
      pure (Rule c args expressions)
    application e
      | get "tag" e == String "apply" = Right (get "value" (get "argument" e))
      | otherwise = refuse Syntax "Constructor result has non-application eliminations"
    term args bindings expected t = fmap (located "native.relation-endpoint" t (toJSON bindings)) $ do
      unless (null (array (get "eliminations" t))) (refuse Syntax "Relation endpoint has nontrivial eliminations")
      case string (get "tag" t) of
        "variable" -> do
          i <- case get "index" t of Number n -> maybe (refuse Syntax "Invalid witness index") Right (toBoundedInteger n); _ -> refuse Syntax "Missing witness index"
          position <- case drop i bindings of
            p:_ | i >= 0 -> Right p
            _ -> refuse Syntax "Relation endpoint is outside its checked binding environment"
          case drop position args of
            actual:_ | position >= 0 && actual == expected -> Right (Witness position)
            _ -> refuse Semantics "Relation witness has an incompatible type or binding"
        "constructor" -> case expected of
          Boolean | get "symbol" t == String (builtin "true") -> Right (BooleanValue True)
                  | get "symbol" t == String (builtin "false") -> Right (BooleanValue False)
          Enumeration shape | string (get "symbol" t) `elem` F.constructors shape -> Right (EnumValue shape (string (get "symbol" t)))
          _ -> refuse Semantics "Relation endpoint is not a constructor of its index domain"
        _ -> refuse Syntax "Relation endpoint expression needs another native rule"

-- Witness positions follow the complete telescope. The de Bruijn environment
-- follows only binding codomains; NoAbs retains the preceding environment.
-- Keeping these separate also preserves unused witnesses in emitted rules.
telescope :: Value -> Either Refusal ([Value],[Int],Value)
telescope = go [] []
  where
    go args bindings ty = let t = get "term" ty in
      if get "tag" t /= String "pi" then Right (args,bindings,ty) else do
        let cod = get "codomain" t
        binds <- case get "binds" cod of
          Bool b -> Right b
          _ -> refuse Syntax "Relation telescope is missing checked binding metadata"
        let next = if binds then length args : bindings else bindings
        go (args ++ [get "type" (get "domain" t)]) next (get "body" cod)

quote :: Text -> Text
quote x = "'" <> T.replace "'" "\\'" (T.replace "\\" "\\\\" x) <> "'"

render :: (Text -> Text) -> Relation -> [Text]
render label = T.lines . D.render . renderDoc label

renderDoc :: (Text -> Text) -> Relation -> D.Doc
renderDoc label rel = mconcat (map renderRule (rules rel)) <> constraint (relationSymbol rel) indexParameters
  (D.mark (relationSymbol rel) "relation-existence-boundary" (D.generated "native.relation-existence") $
    D.text (if null (rules rel) then "false" else T.intercalate " or " (map existential (rules rel))))
  where
    typ Boolean = "Boolean"
    typ (Enumeration shape) = quote (label (F.domainSymbol shape))
    input i = "input" <> T.pack (show i)
    witness i = "witness" <> T.pack (show i)
    indexParameters = zipWith (\i t -> (input i,t)) [0 :: Int ..] (indices rel)
    witnessParameters rule = zipWith (\i t -> (witness i,t)) [0 :: Int ..] (witnesses rule)
    value (Witness i) = quote (witness i)
    value (BooleanValue True) = "true"
    value (BooleanValue False) = "false"
    value (EnumValue shape c) = quote (label (F.domainSymbol shape)) <> "::" <> quote (label c)
    constraint symbol parameters body = D.mark symbol "relation-constraint"
      (D.derived "native.relation" [D.root symbol "type"] Null []) $
      D.linesDoc ([D.text ("  constraint def " <> quote (label symbol) <> " {")]
      ++ [D.text ("    in " <> quote name <> " : " <> typ t <> ";") | (name,t) <- parameters]
      ++ ["    " <> body,"  }"])
    renderRule rule = constraint (ruleSymbol rule) (indexParameters ++ witnessParameters rule)
      (D.joinDoc " and " [D.mark (ruleSymbol rule) "endpoint-equality" (annotation endpoint)
        ("(" <> D.text (quote (input i)) <> " == "
         <> D.mark (ruleSymbol rule) "relation-endpoint" (annotation endpoint) (D.text (value endpoint)) <> ")")
        | (i,endpoint) <- zip [0 :: Int ..] (endpoints rule)])
    existential rule = "(" <> foldr quantify call (witnessParameters rule) <> ")"
      where
        call = quote (label (ruleSymbol rule)) <> "(" <> T.intercalate ", "
          [quote name | (name,_) <- indexParameters ++ witnessParameters rule] <> ")"
        quantify (name,t) body = "(all " <> typ t <> ")->exists { in " <> quote name <> " : " <> typ t <> "; " <> body <> " }"
