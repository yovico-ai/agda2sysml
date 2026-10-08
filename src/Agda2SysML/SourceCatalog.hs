{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Agda2SysML.SourceCatalog
  ( SyntaxNode(..), navigation, catalog, attachOwners, collect, validateClauseReplay, validateClauseCoverage ) where

import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as N
import Agda.Syntax.Common (unArg, namedThing)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (ScopeInfo(..))
import Agda2SysML.Sharing (digest, expand)
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Bifunctor (first)
import Control.Monad (forM_, unless)
import Data.Foldable (toList)
import Data.List (scanl', nub, sort)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Aeson.Key as K
import qualified Data.Vector as V
import Data.Scientific (toBoundedInteger)

data SyntaxNode = SyntaxNode Text Range (Maybe Range) (Maybe Text) [SyntaxNode]

navigation :: Range -> Value
navigation r = object ["start" .= fmap position (rStart r), "end" .= fmap position (rEnd r)]
  where position p = object ["line" .= posLine p,"column" .= posCol p]

get :: Key -> Value -> Value
get key (Object fields) = maybe Null id (KM.lookup key fields)
get _ _ = Null
array :: Value -> [Value]
array (Array xs) = toList xs
array _ = []
set :: Key -> Value -> Value -> Value
set key value (Object fields) = Object (KM.insert key value fields)
set _ _ value = value

-- Positions count compiler characters, not UTF-8 bytes. Use Agda's own cursor
-- movement (including tabs/newlines) and validate both cursor coordinates.
catalog :: Text -> Text -> [SyntaxNode] -> Value
catalog moduleName contents roots = object
  ["version" .= (1 :: Int),"coordinateSystem" .= ("utf8-byte-offsets-zero-based-half-open" :: Text)
  ,"checkedTextDigest" .= digest (TE.encodeUtf8 contents)
  ,"occurrences" .= concat [walk Nothing Nothing [i] node | (i,node) <- zip [0..] roots]]
  where
    positions = M.fromList [(posPos p,(p,bytes)) | (p,bytes) <- scanl' advance (startPos Nothing,0 :: Int) (T.unpack contents)]
    advance (p,bytes) c = (movePos p c,bytes + BS.length (TE.encodeUtf8 (T.singleton c)))
    offset p = do
      (cursor,n) <- M.lookup (posPos p) positions
      if posLine p == posLine cursor && posCol p == posCol cursor then Just n else Nothing
    interval i = do
      a <- offset (iStart' i); b <- offset (iEnd' i)
      if a < b then Just (object ["start" .= a,"end" .= b]) else Nothing
    identifier path = TE.decodeUtf8 (BL.toStrict (encode (moduleName,path)))
    walk :: Maybe Text -> Maybe Text -> [Int] -> SyntaxNode -> [Value]
    walk parent inherited path (SyntaxNode role range binding limitation children) =
      let key = identifier path
          anchor = case binding of Just _ -> Just key; Nothing -> inherited
          ranges = rangeIntervals range
          converted = traverse interval ranges
          unavailable = if null ranges then Just ("source-range-unavailable" :: Text)
            else case converted of Nothing -> Just "invalid-source-range"; Just _ -> Nothing
          entry = object ["id" .= key,"module" .= moduleName,"path" .= path,"parent" .= parent
            ,"role" .= role,"anchor" .= anchor,"binding" .= fmap navigation binding
            ,"navigation" .= navigation range,"intervals" .= maybe [] id converted
            ,"rangeUnavailable" .= unavailable,"syntaxUnavailable" .= limitation]
      in entry : concat [walk (Just key) anchor (path ++ [i]) child | (i,child) <- zip [0..] children]

-- Run after root merging, so ownership does not depend on traversal order or
-- whether a declaration was initially discovered as imported signature support.
attachOwners :: Value -> Either Text Value
attachOwners inventory = do
  table <- case fromJSON (get "nodes" inventory) of Success x -> Right x; Error e -> Left (T.pack e)
  let moduleCatalog md = do
        definitions <- traverse (\d -> first T.pack $ expand table $ object
          [k .= get k d | k <- ["name","bindingModule","source","withParent"]]) (array (get "definitions" md))
        let syntax = get "sourceCorrespondence" md
            occurrences = array (get "occurrences" syntax)
            candidates occurrence = sort . nub $
              [get "name" d | d <- definitions,get "bindingModule" d == get "name" md
              ,get "binding" occurrence /= Null
              ,get "start" (get "binding" occurrence) /= Null
              ,get "source" d == get "binding" occurrence]
            owners = M.fromList [(get "id" o,candidates o) | o <- occurrences,get "binding" o /= Null]
            attach occurrence = let
              matches = M.findWithDefault [] (get "anchor" occurrence) owners
              (owner,reason) = case matches of
                [symbol] -> (symbol,Null)
                [] -> (Null,String "source-anchor-unavailable")
                _ -> (Null,String "source-anchor-ambiguous")
              in set "owner" owner $ set "ownerUnavailable" reason $ set "ownerCandidates" (toJSON matches) occurrence
            attached = map attach occurrences
            declarationAnchor d = let
              ids = [get "id" o | o <- attached,get "binding" o /= Null,get "owner" o == get "name" d]
              ambiguity = any (elem (get "name" d) . array . get "ownerCandidates") attached
              reason | not (null ids) = Null
                     | ambiguity = String "source-anchor-ambiguous"
                     | get "withParent" d /= Null = String "compiler-generated-origin-unresolved"
                     | otherwise = String "source-anchor-unavailable"
              in object ["symbol" .= get "name" d,"occurrences" .= ids,"unavailable" .= reason
                ,"contextOwner" .= get "withParent" d]
        forM_ (concat [array (get part (get "sourceAlignment" md)) | part <- ["definitions","signatures"]]) $ \alignment -> do
          let links = array (get "links" alignment)
              owner = get "owner" alignment
          unless (null links || get "unavailable" alignment == Null) (Left "source-alignment-inconsistent-status")
          forM_ links $ \link -> do
            let locator = get "checked" link
                sources = [o | o <- attached,get "id" o == get "source" link]
                clauses = if get "rule" link == String "source.explicit-signature"
                  then [o | o <- attached,get "id" o == get "signature" link,get "role" o `elem` [String "function-signature",String "constructor-signature"]]
                  else [o | o <- attached,get "id" o == get "clause" link,get "role" o == String "clause"]
            unless (get "owner" locator == owner && length sources == 1 && length clauses == 1
              && all ((== owner) . get "owner") (sources ++ clauses)) (Left "source-alignment-invalid-source")
            d <- case [d | d <- array (get "definitions" md),get "name" d == owner] of
              [d] -> Right d
              _ -> Left "source-alignment-unresolved-owner"
            key <- case get "root" locator of
              String r | r `elem` ["clauses","compiled","type"] -> Right (K.fromText r)
              _ -> Left "source-alignment-invalid-root"
            value <- first T.pack (expand table (get key d))
            unless (descend value (array (get "path" locator)) /= Nothing) (Left "source-alignment-invalid-path")
            unless (get "ruleVersion" link == Number 1) (Left "source-alignment-invalid-rule")
            case get "rule" link of
              String "source.direct-first-order" -> unless (get "root" locator `elem` [String "clauses",String "compiled"])
                (Left "source-alignment-invalid-root")
              String "source.explicit-signature" -> unless (get "root" locator == String "type"
                && all ((== get "signature" link) . get "anchor") sources)
                (Left "source-alignment-invalid-signature")
              String "source.compiled-clause" -> do
                validateClauseReplay value link
                validateClauseCoverage value (get "path" locator)
                  [l | l <- links,get "checked" l == locator]
                unless (any (\body -> get "rule" body == String "source.direct-first-order"
                  && get "clause" body == get "clause" link && get "checkedClause" body == get "checkedClause" link
                  && get "bindings" body == get "bindings" link
                  && get "root" (get "checked" body) == String "compiled"
                  && get "path" (get "checked" body) == toJSON (array (get "leaf" (get "replay" link)) ++ [String "body"])) links)
                  (Left "source-alignment-missing-leaf-evidence")
              _ -> Left "source-alignment-invalid-rule"
        pure $ set "sourceCorrespondence"
          (set "declarationAnchors" (toJSON (map declarationAnchor definitions)) $
           set "occurrences" (toJSON attached) syntax) md
  modules <- traverse moduleCatalog (array (get "modules" inventory))
  pure (set "modules" (toJSON modules) inventory)
  where
    descend value [] = Just value
    descend (Object fs) (String k:rest) = KM.lookup (K.fromText k) fs >>= (\v -> descend v rest)
    descend (Array xs) (Number n:rest) | Just i <- toBoundedInteger n = (xs V.!? i) >>= (\v -> descend v rest)
    descend _ _ = Nothing

-- Validate the structural replay certificate against the actual compiled root.
-- The producer has already established source/checked pattern and RHS alignment;
-- this check prevents a serialized link from drifting to another case or leaf.
validateClauseReplay :: Value -> Value -> Either Text ()
validateClauseReplay tree link = do
  unless (get "root" locator == String "compiled" && get "source" link == get "clause" link
    && get "replay" link /= Null) bad
  (leafValue,paths) <- walk [] tree (array (get "splits" certificate))
  let permutation = array (get "binderPermutation" certificate)
  unless (get "tag" leafValue == String "done" && get "leaf" certificate == toJSON (last paths)
    && array (get "path" locator) `elem` paths
    && length permutation == length (array (get "binders" leafValue))
    && length permutation == length (nub permutation)
    && all validIndex permutation) bad
  where
    locator = get "checked" link
    certificate = get "replay" link
    bad = Left "source-alignment-invalid-replay"
    validIndex (Number n) = case toBoundedInteger n :: Maybe Int of Just i -> i >= 0; _ -> False
    validIndex _ = False
    walk path value [] = Right (value,[path])
    walk path value (step:rest) = do
      j <- case get "branch" step of
        Number n | Just i <- toBoundedInteger n, i >= (0 :: Int) -> Right i
        _ -> bad
      branch <- case drop j (array (get "constructors" value)) of b:_ -> Right b; _ -> bad
      let child = path ++ [String "constructors",toJSON j,String "branch",String "tree"]
          subtree = get "branch" branch
      unless (get "tag" value == String "case" && get "path" step == toJSON path
        && get "argument" step == get "value" (get "argument" value)
        && get "constructor" step == get "symbol" branch && get "arity" step == get "arity" subtree
        && get "child" step == toJSON child) bad
      (leafValue,paths) <- walk child (get "tree" subtree) rest
      pure (leafValue,path:paths)

-- A case occurrence requires every descendant clause. One valid branch cannot
-- justify the whole case; duplicate certificates cannot stand in for coverage.
validateClauseCoverage :: Value -> Value -> [Value] -> Either Text ()
validateClauseCoverage tree nodePath links = do
  node <- maybe bad Right (descend tree (array nodePath))
  expected <- leaves (array nodePath) node
  let actual = [array (get "leaf" (get "replay" l)) | l <- links
        , get "rule" l == String "source.compiled-clause"]
  unless (sort actual == sort expected && not (null expected)) bad
  where
    bad = Left "source-alignment-incomplete-case-coverage"
    descend value [] = Just value
    descend (Object fs) (String k:rest) = KM.lookup (K.fromText k) fs >>= (\v -> descend v rest)
    descend (Array xs) (Number n:rest) | Just i <- toBoundedInteger n = (xs V.!? i) >>= (\v -> descend v rest)
    descend _ _ = Nothing
    leaves path value = case get "tag" value of
      String "done" -> Right [path]
      String "case" | get "eta" value == Null && get "catchall" value == Null
        && null (array (get "literals" value)) -> concat <$> sequence
          [leaves (path ++ [String "constructors",toJSON i,String "branch",String "tree"]) (get "tree" (get "branch" b))
            | (i,b) <- zip [0 :: Int ..] (array (get "constructors" value))]
      _ -> bad

leaf :: Text -> Range -> SyntaxNode
leaf role range = SyntaxNode role range Nothing Nothing []
unsupported :: Range -> Text -> SyntaxNode
unsupported range reason = SyntaxNode "unsupported-syntax" range Nothing (Just reason) []

collect :: ScopeInfo -> [C.Declaration] -> [SyntaxNode]
collect scope = declarations C.NoWhere_
  where
    declarations context ds = case fst $ N.runNice (N.NiceEnv False context) $
      N.niceDeclarations (_scopeFixities scope) ds of
        Left _ -> [unsupported (getRange ds) "source-grouping-unavailable"]
        Right nice -> map visit nice
    node role r children = SyntaxNode role r Nothing Nothing children
    named role r n children = SyntaxNode role r (Just (getRange n)) Nothing children
    visit = \case
      N.FunSig r _ _ _ _ _ _ _ n ty -> named "function-signature" r n [expression ty]
      N.FunDef r _ _ _ _ _ n clauses -> named "function" r n (map clause clauses)
      N.Axiom r _ _ _ _ n ty -> named "type-signature" r n [expression ty]
      N.NiceField r _ _ _ _ n ty -> named "field-signature" r n [expression (unArg ty)]
      N.PrimitiveFunction r _ _ n ty -> named "primitive-signature" r n [expression (unArg ty)]
      N.NiceDataSig r _ _ _ _ _ n bs ty -> named "datatype-signature" r n (map binding bs ++ [expression ty])
      N.NiceRecSig r _ _ _ _ _ n bs ty -> named "record-signature" r n (map binding bs ++ [expression ty])
      N.NiceDataDef r _ _ _ _ n bs cs -> named "datatype" r n (map binding bs ++ map constructor cs)
      N.NiceRecDef r _ _ _ _ n directives bs ds -> named "record" r n
        (map directive directives ++ map binding bs ++ declarations C.NoWhere_ ds)
      N.NiceLoneConstructor r cs -> node "constructors" (getRange r) (map constructor cs)
      N.NiceModule r _ _ _ _ tel ds -> node "module" r (map typedBinding tel ++ declarations C.NoWhere_ ds)
      N.NiceMutual r _ _ _ ds -> node "mutual" (getRange r) (map visit ds)
      N.NiceOpaque r _ ds -> node "opaque" (getRange r) (map visit ds)
      N.NiceFunClause r _ _ _ _ _ _ -> unsupported r "source-anchor-unavailable"
      N.NiceOpen r _ _ -> leaf "open" r
      N.NiceImport r _ _ _ _ -> leaf "import" r
      N.NicePragma r _ -> leaf "pragma" r
      d -> unsupported (getRange d) "declaration-syntax-unavailable"
    constructor d = case visit d of SyntaxNode _ r b reason children -> SyntaxNode "constructor-signature" r b reason children
    directive (C.Constructor n _) = named "record-constructor" (getRange n) n []
    directive d = leaf "record-directive" (getRange d)
    clauseRange (N.Clause _ _ lhs rhs wh _) = getRange lhs `fuseRange` rhs `fuseRange` wh
    clause (N.Clause _ _ lhs rhs wh children) = node "clause" (getRange lhs `fuseRange` rhs `fuseRange` wh)
      ([leaf "pattern" (getRange (C.lhsOriginalPattern lhs))]
        ++ [node "with-expression" (getRange e) [expression (unArg (namedThing e))] | e <- C.lhsWithExpr lhs]
        ++ [node "rewrite-expression" (getRange e) (map expression (toList e)) | e <- C.lhsRewriteEqn lhs]
        ++ [case rhs of C.RHS e -> node "rhs" (getRange rhs) [expression e]; _ -> leaf "rhs" (getRange rhs)]
        ++ whereNodes wh ++ [node "with-clauses" (mconcat (map clauseRange children)) (map clause children) | not (null children)])
    whereNodes C.NoWhere = []
    whereNodes wh@(C.AnyWhere _ ds) = [node "where" (getRange wh) (declarations (C.whereClause_ wh) ds)]
    whereNodes wh@(C.SomeWhere _ _ _ _ ds) = [node "where" (getRange wh) (declarations (C.whereClause_ wh) ds)]
    binding (C.DomainFree b) = leaf "binder" (getRange b)
    binding (C.DomainFull b) = typedBinding b
    typedBinding (C.TBind r names ty) = node "typed-binding" r
      (map (leaf "binder" . getRange) (toList names) ++ [expression ty])
    typedBinding (C.TLet r ds) = node "let-binding" r (declarations C.NoWhere_ (toList ds))
    expression e = let expr role children = node role (getRange e) children in case e of
      C.Ident{} -> expr "identifier" []
      C.KnownIdent{} -> expr "identifier" []
      C.Lit{} -> expr "literal" []
      C.RawApp _ es -> expr "raw-application" (map expression (toList es))
      C.App _ f a -> expr "application" [expression f,expression (namedThing (unArg a))]
      C.WithApp _ f es -> expr "with-application" (map expression (f:toList es))
      C.Paren _ x -> expr "parenthesized" [expression x]
      C.HiddenArg _ a -> expr "hidden-argument" [expression (namedThing a)]
      C.InstanceArg _ a -> expr "instance-argument" [expression (namedThing a)]
      C.Fun _ a b -> expr "function-type" [expression (unArg a),expression b]
      C.Pi tel b -> expr "dependent-function-type" (map typedBinding (toList tel) ++ [expression b])
      C.Lam _ bs body -> expr "lambda" (map binding (toList bs) ++ [expression body])
      C.Let _ ds body -> expr "let" (declarations C.NoWhere_ (toList ds) ++ maybe [] (pure . expression) body)
      C.Dot _ x -> expr "dot" [expression x]
      C.DoubleDot _ x -> expr "double-dot" [expression x]
      C.As _ n x -> expr "as" [leaf "binder" (getRange n),expression x]
      C.Equal _ a b -> expr "equality" [expression a,expression b]
      C.DontCare x -> expr "irrelevant" [expression x]
      C.Generalized x -> expr "generalized" [expression x]
      C.Underscore{} -> expr "underscore" []
      C.QuestionMark{} -> expr "hole" []
      C.Absurd{} -> expr "absurd" []
      C.Ellipsis{} -> expr "ellipsis" []
      _ -> unsupported (getRange e) "expression-syntax-unavailable"
