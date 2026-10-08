{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Agda2SysML.FiniteTarget (Domain(..), Expression(Value, Input, Select), domain, function, render, renderDoc, enumText) where

import qualified Agda2SysML.Derivation as D
import Agda2SysML.Inventory hiding (field)
import Agda2SysML.Diagnostic
import Control.Monad (unless, forM_)
import Data.Aeson
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

data Domain = Domain { domainSymbol :: Text, constructors :: [Text] } deriving (Eq, Show)
data Expression = Annotated D.Origin Expression
  | NValue Text
  | NInput Int
  | NSelect Expression (NonEmpty (Text,Expression))
  deriving Show

unmark :: Expression -> Expression
unmark (Annotated _ x) = unmark x
unmark x = x

instance Eq Expression where
  x == y | NValue a0 <- unmark x, NValue b0 <- unmark y = a0 == b0
  x == y | NInput a0 <- unmark x, NInput b0 <- unmark y = a0 == b0
  x == y | NSelect a0 a1 <- unmark x, NSelect b0 b1 <- unmark y = a0 == b0 && a1 == b1
  _ == _ = False
pattern Value :: Text -> Expression
pattern Value c <- (unmark -> NValue c) where Value c = NValue c
pattern Input :: Int -> Expression
pattern Input i <- (unmark -> NInput i) where Input i = NInput i
pattern Select :: Expression -> NonEmpty (Text,Expression) -> Expression
pattern Select d bs <- (unmark -> NSelect d bs) where Select d bs = NSelect d bs
{-# COMPLETE Value, Input, Select #-}

annotation :: Expression -> D.Origin
annotation (Annotated o _) = o
annotation _ = D.generated "native.generated-expression"

located :: Text -> Value -> Value -> Expression -> Expression
-- A fresh root gets its first justified origin here. Existing annotations,
-- including explicit unavailable boundaries, must survive unchanged as premises.
located rule input premises e = Annotated (D.origin rule input premises parents) e
  where parents = case e of Annotated o _ -> [o]; _ -> []


integer :: Value -> Either Refusal Int
integer (Number n) = maybe (refuse Syntax "Invalid checked index") Right (toBoundedInteger n)
integer _ = refuse Syntax "Missing checked index"

at :: Int -> [a] -> Either Refusal a
at i xs = case drop i xs of
  x:_ | i >= 0 -> Right x
  _ -> refuse Syntax "Case-tree reference is outside its binding environment"

definitionType :: Value -> Maybe Text
definitionType ty = let t = get "term" ty in
  if get "tag" t == String "definition" && get "eliminations" t == toJSON ([] :: [Value])
  then Just (string (get "symbol" t)) else Nothing

domain :: Inventory -> Value -> Either Refusal Domain
domain inv d = do
  unless (get "kind" d == String "datatype" && get "abstract" d == Bool False) $
    refuse Representation "The finite domain rule requires a concrete datatype"
  parameters <- field inv "parameters" d >>= integer
  ty <- field inv "type" d
  unless (parameters == 0 && get "tag" (get "term" ty) == String "sort") $
    refuse Representation "The finite domain rule requires a closed type without parameters or indices"
  cs <- map string . array <$> field inv "constructors" d
  unless (not (null cs) && S.size (S.fromList cs) == length cs) $
    refuse Representation "The finite domain rule requires a nonempty set of distinct constructors"
  let symbol = string (get "name" d)
  forM_ cs $ \c -> do
    constructor <- maybe (refuse Syntax "Missing checked constructor") Right (M.lookup c (declarations inv))
    constructorType <- field inv "type" constructor
    unless (get "kind" constructor == String "constructor" && definitionType constructorType == Just symbol) $
      refuse Representation "The finite domain rule does not admit constructor payloads"
  pure (Domain symbol cs)

function :: Inventory -> M.Map Text Domain -> Value -> Either Refusal (Domain,Int,Expression)
function inv domains d = do
  unless (length (array (get "sourceSyntax" d)) == 1) (refuse Syntax "No uniquely anchored source definition")
  ty <- field inv "type" d
  (inputs,result) <- telescope ty
  symbol <- maybe (refuse Representation "Result needs a different domain rule") Right (definitionType result)
  shape <- maybe (refuse Representation "Result has no finite domain representation") Right (M.lookup symbol domains)
  unless (all ((== Just symbol) . definitionType) inputs) $
    refuse Representation "This finite case rule requires every input to belong to the result domain"
  tree <- field inv "compiled" d
  body <- lower shape [Input i | i <- [0..length inputs-1]] tree
  pure (shape,length inputs,body)
  where
    telescope ty = let t = get "term" ty in if get "tag" t == String "pi" then do
      (rest,result) <- telescope (get "body" (get "codomain" t))
      pure (get "type" (get "domain" t) : rest,result)
      else Right ([],ty)
    lower shape env tree = fmap (located "native.finite-case" tree (toJSON [render id shape x | x <- env])) $ case string (get "tag" tree) of
      "done" -> do
        unless (length (array (get "binders" tree)) == length env) (refuse Syntax "Case leaf has an inconsistent binder count")
        expression shape (reverse env) (get "body" tree)
      "case" -> do
        unless (get "copattern" tree == Bool False && get "eta" tree == Null
          && null (array (get "literals" tree)) && get "catchall" tree == Null
          && get "lazy" tree == Bool False && get "fallThrough" tree == Bool False) $
          refuse Semantics "This case tree requires an additional match rule"
        i <- integer (get "value" (get "argument" tree))
        selected <- at i env
        let branches = array (get "constructors" tree)
            symbols = map (string . get "symbol") branches
            reduced = take i env ++ drop (i+1) env
        unless (length symbols == length (constructors shape) && S.fromList symbols == S.fromList (constructors shape)) $
          refuse Semantics "Finite constructor branches are not exhaustive and distinct"
        lowered <- traverse (\c -> case filter ((== String c) . get "symbol") branches of
          [b] | get "arity" (get "branch" b) == Number 0 ->
            (c,) <$> lower shape reduced (get "tree" (get "branch" b))
          _ -> refuse Representation "Finite case matching encountered a constructor payload") (constructors shape)
        case lowered of
          first:rest -> pure (Select (located "native.finite-discriminant" tree (toJSON i) selected) (first :| rest))
          [] -> refuse Semantics "Empty constructor coverage"
      _ -> refuse Syntax "This compiled body needs a rule beyond finite constructor cases"
    expression shape env t = fmap (located "native.finite-term" t (toJSON [render id shape x | x <- env])) $ do
      unless (null (array (get "eliminations" t))) (refuse Syntax "Leaf eliminations need a separate rule")
      case string (get "tag" t) of
        "variable" -> integer (get "index" t) >>= (`at` env)
        "constructor" | string (get "symbol" t) `elem` constructors shape -> Right (Value (string (get "symbol" t)))
        _ -> refuse Syntax "Leaf expression needs another native target rule"

quote :: Text -> Text
quote x = "'" <> T.replace "'" "\\'" (T.replace "\\" "\\\\" x) <> "'"

-- The final alternative is reached only after every other distinct constructor
-- has failed equality. Applicability has established a nonempty exhaustive set.
render :: (Text -> Text) -> Domain -> Expression -> Text
render label shape = D.render . renderDoc label "" shape

renderDoc :: (Text -> Text) -> Text -> Domain -> Expression -> D.Doc
renderDoc label owner shape = go
  where
    constructor c = D.text (quote (label (domainSymbol shape)) <> "::" <> quote (label c))
    go e = D.mark owner "finite-expression" (annotation e) $ case e of
      Value c -> constructor c
      Input i -> D.text (quote ("input" <> T.pack (show i)))
      Select discriminant branches -> choose (annotation e) discriminant branches
    choose _ _ ((_,lastBranch) :| []) = go lastBranch
    choose evidence discriminant ((c,branch) :| next:rest) = D.mark owner "finite-choice"
      (D.derived "native.finite-choice" [] (object ["constructor" .= c]) [evidence]) $
      "(if " <> D.mark owner "finite-constructor-test"
        (D.derived "native.finite-test" [] (object ["constructor" .= c]) [evidence])
        (go discriminant <> " == " <> constructor c)
      <> " ? " <> go branch <> " else " <> choose evidence discriminant (next :| rest) <> ")"

enumText :: (Text -> Text) -> Domain -> [Text]
enumText label shape = ["  enum def " <> quote (label (domainSymbol shape)) <> " {"]
  ++ ["    enum " <> quote (label c) <> ";" | c <- constructors shape] ++ ["  }"]
