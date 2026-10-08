{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Agda2SysML.Mapping
  ( Mapping(..), Model(..), State(..), Selector(..), Transition(..), Result(..)
  , Invariant(..), readMapping, parseMapping, references ) where

import Control.Monad (unless, when)
import Control.Exception (try)
import Control.Monad.Trans.Resource (runResourceT)
import Data.Conduit ((.|), runConduit)
import qualified Data.Conduit.List as CL
import qualified Data.ByteString as BS
import Data.Char (isAscii, isAlpha, isAlphaNum)
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Numeric (readHex, readOct)
import Text.Read (readMaybe)
import Text.Regex.TDFA ((=~))
import qualified Text.Libyaml as Y

data Mapping = Mapping { mappingVersion :: Int, projectName :: Text, library :: FilePath
  , roots :: [Text], inventoryLibrary :: Bool, models :: M.Map Text Model } deriving (Show, Eq)
data Model = Model { modelModule :: Text, title :: Text, state :: State
  , commands :: Maybe Text, transition :: Transition
  , invariants :: [Invariant], theorems :: [Text] } deriving (Show, Eq)
data State = NamedState Text | InferState deriving (Show, Eq)
data Selector = Binder Text | Position Int deriving (Show, Eq)
data Transition = Function Text (Maybe Selector) Selector Result | Relation Text Int Int deriving (Show, Eq)
data Result = DirectState | Family Text Text (M.Map Text Text) deriving (Show, Eq)
data Invariant = Invariant Text (Maybe Selector) deriving (Show, Eq)

-- Scalar types are decided here with YAML 1.2 core rules, not libyaml's loader.
data Node = Node Int Int Val deriving Show
data Val = Str Text | IntVal Integer | OtherScalar | Boolean Bool
         | List [Node] | Dict (M.Map Text Node) deriving Show
type Check a = Either String a

err :: Node -> String -> Check a
err (Node l c _) msg = Left ("invalid-mapping at " ++ show l ++ ":" ++ show c ++ ": " ++ msg)

readMapping :: FilePath -> IO (Check Mapping)
readMapping file = BS.readFile file >>= parseMapping

parseMapping :: BS.ByteString -> IO (Check Mapping)
parseMapping bytes = do
  decoded <- try $ runResourceT $ runConduit $ Y.decodeMarked bytes .| CL.consume
  pure $ case decoded of
    Left (e :: Y.YamlException) -> Left ("invalid-mapping: " ++ show e)
    Right events -> document events
  where
   document events = case events of
    a:b:rest | Y.yamlEvent a == Y.EventStreamStart, Y.yamlEvent b == Y.EventDocumentStart -> do
      (root, tailEvents) <- node rest
      case map Y.yamlEvent tailEvents of
        [Y.EventDocumentEnd,Y.EventStreamEnd] -> mapping root
        _ -> err root "exactly one document is required"
    _ -> Left "invalid-mapping: expected one YAML document"

node :: [Y.MarkedEvent] -> Check (Node, [Y.MarkedEvent])
node [] = Left "invalid-mapping: unexpected end of input"
node (e:es) = case Y.yamlEvent e of
  Y.EventScalar bytes tag style anchor -> do
    noAnchor anchor
    txt <- either (const $ err here "invalid UTF-8") Right (TE.decodeUtf8' bytes)
    v <- scalar here tag style txt
    pure (located v,es)
  Y.EventSequenceStart tag _ anchor -> do
    noAnchor anchor
    tagIs [Y.NoTag,Y.SeqTag] tag
    (xs,rest) <- sequenceNodes es
    pure (located (List xs),rest)
  Y.EventMappingStart tag _ anchor -> do
    noAnchor anchor
    tagIs [Y.NoTag,Y.MapTag] tag
    (xs,rest) <- mappingNodes M.empty es
    pure (located (Dict xs),rest)
  Y.EventAlias _ -> err here "aliases are not supported"
  _ -> err here "expected scalar, sequence, or mapping"
  where
    mark = Y.yamlStartMark e
    located = Node (Y.yamlLine mark + 1) (Y.yamlColumn mark + 1)
    here = located OtherScalar
    noAnchor = maybe (Right ()) (const $ err here "anchors are not supported")
    tagIs tags tag = unless (tag `elem` tags) (err here "unsupported tag")
    sequenceNodes xs = case xs of
      a:rest | Y.yamlEvent a == Y.EventSequenceEnd -> Right ([],rest)
      _ -> do (v,ys) <- node xs; (vs,zs) <- sequenceNodes ys; pure (v:vs,zs)
    mappingNodes acc xs = case xs of
      a:rest | Y.yamlEvent a == Y.EventMappingEnd -> Right (acc,rest)
      _ -> do
        (k,ys) <- node xs
        key <- string k
        when (key == "<<") $ err k "merge keys are not supported"
        when (M.member key acc) $ err k ("duplicate key " ++ T.unpack key)
        (v,zs) <- node ys
        mappingNodes (M.insert key v acc) zs

scalar :: Node -> Y.Tag -> Y.Style -> Text -> Check Val
scalar n tag style t
  | tag == Y.StrTag = Right (Str t)
  | tag == Y.NoTag = Right $ if style `elem` [Y.Plain,Y.PlainNoTag,Y.Any] then core else Str t
  | tag == Y.IntTag, IntVal{} <- core = Right core
  | tag == Y.BoolTag, Boolean{} <- core = Right core
  | tag == Y.NullTag, t `elem` ["", "~", "null", "Null", "NULL"] = Right OtherScalar
  | tag == Y.FloatTag, numeric = Right OtherScalar
  | otherwise = err n "unsupported tag or invalid tagged scalar"
  where
    matches re = T.unpack t =~ (re :: String) :: Bool
    numeric = matches "^[-+]?([0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][-+]?[0-9]+)?$"
      || T.toLower t `elem` [".inf","+.inf","-.inf",".nan"]
    core
      | t `elem` ["true","True","TRUE"] = Boolean True
      | t `elem` ["false","False","FALSE"] = Boolean False
      | t `elem` ["", "~", "null", "Null", "NULL"] = OtherScalar
      | matches "^[-+]?[0-9]+$" = maybe OtherScalar IntVal (readMaybe (T.unpack (T.dropWhile (== '+') t)))
      | matches "^0o[0-7]+$", [(v,"")] <- readOct (T.unpack (T.drop 2 t)) = IntVal v
      | matches "^0x[0-9a-fA-F]+$", [(v,"")] <- readHex (T.unpack (T.drop 2 t)) = IntVal v
      | numeric = OtherScalar
      | otherwise = Str t

string :: Node -> Check Text
string n@(Node _ _ v) = case v of
  Str t | not (T.null t) -> Right t
  _ -> err n "expected nonempty string"

integer :: Node -> Check Int
integer n@(Node _ _ v) = case v of
  IntVal i | i >= 0, i <= toInteger (maxBound :: Int) -> Right (fromInteger i)
  _ -> err n "expected nonnegative integer"

dict :: Node -> Check (M.Map Text Node)
dict n@(Node _ _ v) = case v of Dict d -> Right d; _ -> err n "expected mapping"

list :: (Node -> Check a) -> Node -> Check [a]
list f n@(Node _ _ v) = case v of List xs -> traverse f xs; _ -> err n "expected sequence"

fields :: [Text] -> [Text] -> Node -> Check (M.Map Text Node)
fields required optionalKeys n = do
  d <- dict n
  unless (all (`M.member` d) required) $ err n ("required keys: " ++ show required)
  unless (all (`elem` (required ++ optionalKeys)) (M.keys d)) $ err n ("allowed keys: " ++ show (required ++ optionalKeys))
  pure d

at :: (Node -> Check a) -> Text -> M.Map Text Node -> Check a
at f k d = maybe (Left ("invalid-mapping: missing " ++ T.unpack k)) f (M.lookup k d)

optional :: (Node -> Check a) -> Text -> M.Map Text Node -> Check (Maybe a)
optional f k = traverse f . M.lookup k

nonemptyDistinct :: Eq a => Node -> [a] -> Check [a]
nonemptyDistinct n xs = do
  when (null xs || length (nub xs) /= length xs) $ err n "expected nonempty sequence of distinct values"
  pure xs

mapping :: Node -> Check Mapping
mapping n = do
  d <- fields ["mapping-version","project","models"] [] n
  v <- at integer "mapping-version" d
  unless (v `elem` [1,2]) $ Left "unsupported-mapping-version"
  pnode <- at Right "project" d
  p <- fields ["name","agda-library","roots"] (if v == 2 then ["inventory"] else []) pnode
  pn <- at string "name" p
  lib <- at string "agda-library" p
  rs <- at (\x -> list string x >>= nonemptyDistinct x) "roots" p
  inv <- optional string "inventory" p
  unless (inv `elem` [Nothing,Just "roots",Just "library"]) $ err pnode "inventory must be roots or library"
  msnode <- at Right "models" d
  ms <- dict msnode
  when (M.null ms) $ err msnode "models must not be empty"
  parsed <- M.traverseWithKey (model v) ms
  pure (Mapping v pn (T.unpack lib) rs (inv == Just "library") parsed)

model :: Int -> Text -> Node -> Check Model
model v key n = do
  unless (validKey key) $ err n "model key must start with an ASCII letter and contain letters, digits, _ or -"
  d <- fields ["module","state","transition"] ["title","commands","contracts"] n
  m <- at string "module" d
  t <- maybe key id <$> optional string "title" d
  s <- at stateType "state" d
  c <- optional namedType "commands" d
  tr <- at (parseTransition v c) "transition" d
  (is,ts) <- maybe (pure ([],[])) contracts (M.lookup "contracts" d)
  pure (Model m t s c tr is ts)
  where
    validKey k = case T.uncons k of
      Just (h,rest) -> isAscii h && isAlpha h && T.all (\x -> isAscii x && (isAlphaNum x || x `elem` ['_','-'])) rest
      _ -> False
    stateType x = do
      ds <- dict x
      if v == 2 && M.keys ds == ["infer"] then case ds M.! "infer" of
        Node _ _ (Boolean True) -> pure InferState
        _ -> err x "infer must be true"
      else NamedState <$> namedType x
    contracts x = do
      ds <- fields [] ["invariants","theorems"] x
      is <- maybe (pure []) (list inv) (M.lookup "invariants" ds)
      ts <- maybe (pure []) (list string) (M.lookup "theorems" ds)
      when (length (nub is) /= length is || length (nub ts) /= length ts) $ err x "duplicate contract selection"
      pure (is,ts)
    inv x@(Node _ _ (Dict _)) | v == 2 = do
      ds <- fields ["symbol","state-argument"] [] x
      Invariant <$> at string "symbol" ds <*> (Just <$> at selector "state-argument" ds)
    inv x = Invariant <$> string x <*> pure Nothing

namedType :: Node -> Check Text
namedType n = fields ["type"] [] n >>= at string "type"

selector :: Node -> Check Selector
selector n@(Node _ _ (Dict _)) = Position <$> (fields ["position"] [] n >>= at integer "position")
selector n = Binder <$> string n

parseTransition :: Int -> Maybe Text -> Node -> Check Transition
parseTransition v cmd n = do
  d <- dict n
  enc <- at string "encoding" d
  case enc of
    "function" -> do
      _ <- fields ["encoding","symbol","arguments","result"] [] n
      when (v == 1 && cmd == Nothing) $ err n "version 1 function model requires commands"
      s <- at string "symbol" d
      args <- at (fields (["before"] ++ ["command" | cmd /= Nothing]) []) "arguments" d
      before <- at selector "before" args
      command <- optional selector "command" args
      when (command == Just before) $ err n "command and before must be distinct"
      r <- at result "result" d
      pure (Function s command before r)
    "relation" -> do
      _ <- fields ["encoding","symbol","indices"] [] n
      when (cmd /= Nothing) $ err n "relation models cannot select commands"
      s <- at string "symbol" d
      ix <- at (fields ["before","after"] []) "indices" d
      before <- at integer "before" ix
      after <- at integer "after" ix
      when (before == after) $ err n "before and after indices must differ"
      pure (Relation s before after)
    _ -> err n "encoding must be function or relation"
  where
    result x = do
      ds <- dict x
      if v == 2 && M.keys ds == ["state"] then do
        st <- at string "state" ds
        unless (st == "return") $ err x "direct state result must be return"
        pure DirectState
      else do
        _ <- fields ["type","state-projection","variants"] [] x
        ty <- at string "type" ds
        proj <- at string "state-projection" ds
        vs <- at dict "variants" ds >>= traverse string
        unless (all (`elem` ["accepted","unchanged","refused"]) (M.elems vs)) $ err x "invalid result category"
        pure (Family ty proj vs)

references :: Model -> [Text]
references m = nub $ stateRefs ++ maybe [] pure (commands m) ++ transRefs ++ invRefs ++ theorems m
  where
    stateRefs = case state m of NamedState n -> [n]; InferState -> []
    transRefs = case transition m of
      Relation n _ _ -> [n]
      Function n _ _ DirectState -> [n]
      Function n _ _ (Family ty p vs) -> n:ty:p:M.keys vs
    invRefs = [n | Invariant n _ <- invariants m]
