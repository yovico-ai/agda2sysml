{-# LANGUAGE OverloadedStrings #-}
module Agda2SysML.Derivation
  ( Origin, origin, generated, derived, references, annotate, strip, root, signatureShape
  , Doc, text, mark, linesDoc, joinDoc, render, report, renderBundle, boundary, validate ) where

import Agda2SysML.Inventory (Inventory(..), get, string, array)
import qualified Agda2SysML.Inventory as I
import Agda2SysML.Sharing (digest)
import Agda2SysML.SourceCatalog (validateClauseReplay, validateClauseCoverage)
import Data.Aeson
import Control.Monad (unless, forM_)
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.List (nub)
import qualified Data.Map.Strict as M
import Data.Scientific (toBoundedInteger)
import Data.String (IsString(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Vector as V

-- Metadata is carried only in the adapter's expanded views, never in the
-- checked inventory or shared-node keys. Paths identify uses, not equal values.
root :: Text -> Text -> Value
root owner field = object ["owner" .= owner,"root" .= field,"path" .= ([] :: [Value])]

annotate :: Text -> Text -> Value -> Value
annotate owner field = go []
  where
    go path (Object fs) = Object $ KM.insert "$occurrence" locator $
      KM.mapWithKey (\k v -> go (path ++ [String (K.toText k)]) v) (KM.delete "$occurrence" fs)
      where locator = object ["owner" .= owner,"root" .= field,"path" .= path]
    go path (Array xs) = Array (V.imap (\i v -> go (path ++ [toJSON i]) v) xs)
    go _ value = value

strip :: Value -> Value
strip (Object fs) = Object (KM.map strip (KM.delete "$occurrence" fs))
strip (Array xs) = Array (V.map strip xs)
strip value = value

-- Canonical first-order signature structure. Each variable resolves through
-- the actual Abs/NoAbs stack to an absolute telescope slot. Inferred sort
-- wrappers and binder display names are not source type expressions; explicit
-- universe terms, applied receivers, hidden arguments and higher-order types refuse.
signatureShape :: Value -> Maybe Value
signatureShape = telescope 0 []
  where
    telescope depth env ty = case get "tag" (get "term" ty) of
      String "pi" -> do
        let term = get "term" ty; dom = get "domain" term; cod = get "codomain" term
        modality <- info (get "info" dom)
        domain <- carrier env (get "type" dom)
        next <- case get "binds" cod of Bool True -> Just (depth:env); Bool False -> Just env; _ -> Nothing
        body <- telescope (depth+1) next (get "body" cod)
        pure (object ["domain" .= domain,"info" .= modality,"codomain" .= body])
      _ -> carrier env ty
    carrier env ty = do
      let term = get "term" ty
      if get "tag" term /= String "definition" then Nothing else expression env term
    info value = if get "hiding" value == String "explicit" && get "relevance" value == String "relevant"
        && get "quantity" value == String "unrestricted"
      then Just (object ["hiding" .= get "hiding" value,"relevance" .= get "relevance" value,"quantity" .= get "quantity" value])
      else Nothing
    expression env term = do
      let es = array (get "eliminations" term)
      headValue <- case get "tag" term of
        String "variable" | null es || singleProjection es -> do
          i <- case get "index" term of Number n -> toBoundedInteger n; _ -> Nothing
          slot <- if i < (0 :: Int) then Nothing else case drop i env of x:_ -> Just x; _ -> Nothing
          pure (object ["slot" .= (slot :: Int)])
        kind | kind `elem` [String "definition",String "constructor"], String name <- get "symbol" term
          , not (T.null name) -> Just (object ["tag" .= kind,"symbol" .= name])
        _ -> Nothing
      if any ((== String "project") . get "tag") es && get "tag" term /= String "variable"
        then Nothing else Just ()
      arguments <- traverse (application env) es
      pure (object ["head" .= headValue,"arguments" .= arguments])
    singleProjection [e] = get "tag" e == String "project" && case get "symbol" e of
      String s -> not (T.null s)
      _ -> False
    singleProjection _ = False
    application _ e | singleProjection [e] = Just (object ["projection" .= get "symbol" e])
    application env e = do
      if get "tag" e /= String "apply" then Nothing else Just ()
      let a = get "argument" e
      modality <- info (get "info" a)
      value <- expression env (get "value" a)
      pure (object ["info" .= modality,"value" .= value])

data Origin = Origin Text [Value] Value [Origin] (Maybe Text) deriving (Eq,Show)

origin :: Text -> Value -> Value -> [Origin] -> Origin
origin rule value premises parents = Origin rule
  [ref | ref /= Null] (strip premises) (history parents)
  (if ref == Null then Just "checked-origin-unavailable" else Nothing)
  where ref = get "$occurrence" value

generated :: Text -> Origin
generated rule = Origin rule [] Null [] (Just "generated-subtree-origin-unavailable")

derived :: Text -> [Value] -> Value -> [Origin] -> Origin
derived rule refs premises parents = Origin rule refs (strip premises) (history parents) Nothing

-- Flatten event history at composition, so repeated normalizations retain each
-- premise without expanding a binary tree of duplicate provenance.
history :: [Origin] -> [Origin]
history = nub . concatMap (\(Origin r refs p parents unavailable) -> Origin r refs p [] unavailable : parents)

references :: Origin -> [Value]
references (Origin _ refs _ parents _) = nub (refs ++ concatMap references parents)

data Doc = Text Text | Append Doc Doc | Mark Text Text Origin Doc
instance IsString Doc where fromString = Text . T.pack
instance Semigroup Doc where (<>) = Append
instance Monoid Doc where mempty = Text ""
text :: Text -> Doc
text = Text
mark :: Text -> Text -> Origin -> Doc -> Doc
mark = Mark
joinDoc :: Doc -> [Doc] -> Doc
joinDoc _ [] = mempty
joinDoc separator (x:xs) = x <> mconcat [separator <> y | y <- xs]
linesDoc :: [Doc] -> Doc
linesDoc = mconcat . map (<> "\n")

boundary :: Text -> Text -> [Text] -> Doc
boundary owner rule rows = mark owner "generated-structure-boundary"
  (Origin rule [root owner "type"] Null [] (Just "structural-subtree-derivation-unavailable"))
  (linesDoc (map text rows))

data Occurrence = Occurrence Text [Int] Text Origin Int Int deriving Show

-- The same traversal emits bytes and records intervals. Append shifts by byte
-- length, never character count; repeated fragments receive separate paths.
rendered :: Doc -> (Text,[Occurrence])
rendered doc = let (_,parts,items) = go [] 0 doc in (T.concat parts,items)
  where
    go _ start (Text t) = (start + BS.length (TE.encodeUtf8 t),[t],[])
    go path start (Append a b) =
      let (middle,xs,as) = go (path ++ [0]) start a
          (end,ys,bs) = go (path ++ [1]) middle b
      in (end,xs ++ ys,as ++ bs)
    go path start (Mark owner role evidence d) =
      let (end,parts,children) = go (path ++ [0]) start d
          Origin rule refs premises parents limitation = evidence
          combined = Origin rule refs premises
            (history (parents ++ [o | Occurrence _ _ _ o _ _ <- children])) limitation
      in (end,parts,Occurrence owner path role combined start end : children)

render :: Doc -> Text
render = fst . rendered

identifier :: Value -> Text
identifier = TE.decodeUtf8 . BL.toStrict . encode

report :: Inventory -> Inventory -> Doc -> Value
report original inv = snd . renderBundle original inv

renderBundle :: Inventory -> Inventory -> Doc -> (Text,Value)
renderBundle original inv doc = (output, object
  ["version" .= (1 :: Int),"coordinateSystem" .= ("utf8-byte-offsets-zero-based-half-open" :: Text)
  ,"artifact" .= ("model.sysml" :: Text),"artifactDigest" .= digest (TE.encodeUtf8 output)
  ,"checkedOccurrences" .= map checked refs,"checkedRoots" .= map checkedRoot roots
  ,"templateRoots" .= nub (map templateRoot roots)
  ,"rules" .= [object ["id" .= rule,"version" .= (1 :: Int)] | rule <- nub ("native.static-specialization" : concat [rules evidence | Occurrence _ _ _ evidence _ _ <- occurrences])]
  ,"targetOccurrences" .= map target occurrences,"derivations" .= map derivation occurrences
  ,"sourceOccurrences" .= sourceOccurrences
  ,"sourceModules" .= [object ["module" .= get "name" md,"source" .= get "source" md
      ,"checkedTextDigest" .= get "checkedTextDigest" (get "sourceCorrespondence" md)]
      | md <- array (get "modules" (document original)),get "name" md `elem` map (get "module") sourceOccurrences]
  ,"sourceAlignment" .= (if null sourceOccurrences then "unavailable" else "partial" :: Text)
  ,"sourceUnavailable" .= ("source-alignment-incomplete" :: Text)])
  where
    rules (Origin rule _ _ parents _) = rule : concatMap rules parents
    (output,occurrences) = rendered doc
    refs = nub (concat [references evidence | Occurrence _ _ _ evidence _ _ <- occurrences])
    roots = nub [root (string (get "owner" r)) (string (get "root" r)) | r <- refs]
    alignmentIndex = M.fromListWith (++) [(get "checked" link,[link])
      | md <- array (get "modules" (document original))
      , d <- concat [array (get part (get "sourceAlignment" md)) | part <- ["definitions","signatures"]],get "unavailable" d == Null
      , link <- array (get "links" d)]
    sourceLinks ref = case M.lookup (string (get "owner" ref)) (declarations inv) of
      Just d | get "preparationOrigin" d == Null -> M.findWithDefault [] ref alignmentIndex
      Just _ | transportRule ref /= Nothing -> map transport (M.findWithDefault [] ref alignmentIndex)
      _ -> []
      where
        transport (Object fs) = Object (KM.insert "preparation" (object
          ["rule" .= transportRule ref,"ruleVersion" .= (1 :: Int)
          ,"template" .= ref]) fs)
        transport v = v
    -- This transports an independently established source alignment at the
    -- SAME owner/root/path. It never searches for equal terms or source uses.
    -- With zero static arguments, require the entire compiled root to preserve
    -- binders, branches, heads and spines. Preparation rebuilds ArgInfo without
    -- its redundant textual modality; retain the original in templateRoots.
    -- Signature transport separately validates resolved telescope structure,
    -- including rebasing across rebuilt Abs/NoAbs binders.
    transportRule ref = M.findWithDefault Nothing
      (root (string (get "owner" ref)) (string (get "root" ref))) preparationIdentity
    preparationIdentity = M.fromList [(ref,identity ref) | ref <- roots]
    identity ref = case (M.lookup (string (get "owner" ref)) (declarations inv),resolveRoot ref) of
      (Just d,Just value) | get "preparationOrigin" d == get "owner" ref
        , get "specializationArguments" d == toJSON ([] :: [Value]) ->
          case M.lookup (string (get "owner" ref)) (declarations original)
            >>= either (const Nothing) Just . I.field original (string (get "root" ref)) of
            Just before | get "root" ref == String "compiled"
              , withoutModality (strip before) == withoutModality value -> Just "source.same-term-structure"
            Just before | get "root" ref == String "type", Just shape <- signatureShape before
              , signatureShape value == Just shape -> Just "source.same-signature-structure"
            _ -> Nothing
      _ -> Nothing
    withoutModality (Object fs) = Object (KM.map withoutModality (KM.delete "modality" fs))
    withoutModality (Array xs) = Array (V.map withoutModality xs)
    withoutModality v = v
    sourceIds = nub [sid | ref <- refs,link <- sourceLinks ref,sourceKey <- ["source","signature"],let sid = get sourceKey link,sid /= Null]
    sourceOccurrences = [o | md <- array (get "modules" (document original))
      ,o <- array (get "occurrences" (get "sourceCorrespondence" md)),get "id" o `elem` sourceIds]
    sourceReady evidence = not (null (references evidence)) && all (not . null . sourceLinks) (references evidence)
      && noBoundary evidence
    noBoundary (Origin _ _ _ parents limitation) = limitation == Nothing && all noBoundary parents
    rootValues = M.fromList [(ref,readRoot ref) | ref <- roots]
    resolveRoot ref = M.findWithDefault Nothing (root (string (get "owner" ref)) (string (get "root" ref))) rootValues
    readRoot ref = do
      d <- M.lookup (string (get "owner" ref)) (declarations inv)
      either (const Nothing) (Just . strip) (I.field inv (string (get "root" ref)) d)
    descend value [] = Just value
    descend (Object fs) (String k:rest) = KM.lookup (K.fromText k) fs >>= (`descend` rest)
    descend (Array xs) (Number n:rest) | Just i <- toBoundedInteger n = (xs V.!? i) >>= (`descend` rest)
    descend _ _ = Nothing
    checked ref = let value = resolveRoot ref >>= (\v -> descend v (array (get "path" ref))) in object
      ["id" .= identifier ref,"owner" .= get "owner" ref,"root" .= get "root" ref,"path" .= get "path" ref
      ,"valueDigest" .= fmap (digest . BL.toStrict . encode) value
      ,"bindingContext" .= context ref
      ,"sourceLinks" .= sourceLinks ref
      ,"sourcePrecision" .= (if null (sourceLinks ref) then "unavailable"
          else if transportRule ref /= Nothing || any ((/= String "source.direct-first-order") . get "rule") (sourceLinks ref)
            then "derived" else "exact" :: Text)
      ,"sourceUnavailable" .= (if null (sourceLinks ref) then Just ("source-alignment-unavailable" :: Text) else Nothing)
      ,"unavailable" .= (if value == Nothing then Just ("checked-occurrence-unavailable" :: Text) else Nothing)]
    context ref = case resolveRoot ref of
      Nothing -> []
      Just value -> walk [] value (array (get "path" ref))
      where
        walk path value remaining =
          [object ["path" .= path,"binders" .= get "binders" value
            ,"binds" .= get "binds" value,"caseArgument" .= get "argument" value]
          | any (/= Null) [get "binders" value,get "binds" value]
            || get "tag" value == String "case"]
          ++ case remaining of
            [] -> []
            part:rest -> maybe [] (\v -> walk (path ++ [part]) v rest) (descend value [part])
    templateRef ref = root template (string (get "root" ref))
      where
        owner = string (get "owner" ref)
        template = case M.lookup owner (declarations inv) of
          Just d | String s <- get "preparationOrigin" d -> s
          _ -> owner
    templateRoot ref = let r = templateRef ref in object
      ["owner" .= get "owner" r,"root" .= get "root" r
      ,"value" .= (M.lookup (string (get "owner" r)) (declarations original)
          >>= either (const Nothing) (Just . strip) . I.field original (string (get "root" r)))]
    checkedRoot ref = object ["owner" .= get "owner" ref,"root" .= get "root" ref
      ,"value" .= resolveRoot ref,"template" .= templateRef ref
      ,"preparation" .= (case M.lookup (string (get "owner" ref)) (declarations inv) of
          Just d | get "preparationOrigin" d /= Null -> object
            ["rule" .= (if hasOpenParameter (get "specializationArguments" d)
                then "native.open-parameter-schema" else "native.static-specialization" :: Text),"ruleVersion" .= (1 :: Int)
            ,"arguments" .= get "specializationArguments" d
            ,"sourceTransport" .= (maybe "unavailable" (T.drop (T.length "source.")) (transportRule ref))
            ,"unavailable" .= ("specialization-subtree-alignment-unavailable" :: Text)]
          _ -> Null)]
    hasOpenParameter (Object fields) = KM.member "openParameter" fields || KM.member "openFamily" fields || any hasOpenParameter (KM.elems fields)
    hasOpenParameter (Array values) = any hasOpenParameter values
    hasOpenParameter _ = False
    key owner path = identifier (toJSON (owner,path))
    target (Occurrence owner path role evidence start end) = object
      ["id" .= key owner path,"owner" .= owner,"path" .= path,"role" .= role
      ,"intervals" .= [object ["start" .= start,"end" .= end]]
      ,"models" .= [model | (model,needs) <- M.toAscList (modelRequirements inv), any ((== owner) . fst) needs]
      ,"obligations" .= [object ["symbol" .= symbol,"kind" .= kind] | (symbol,kind) <- nub (concatMap (foldr (:) []) (M.elems (modelRequirements inv))),symbol == owner]
      ,"derivation" .= key owner path
      ,"sourcePrecision" .= (if sourceReady evidence then "derived" else "unavailable" :: Text)
      ,"checkedPrecision" .= (case evidence of Origin _ _ _ _ (Just _) -> "unavailable"; _ -> if null (references evidence) then "unavailable" else "derived" :: Text)]
    evidenceValue (Origin rule inputs premises parents limitation) = object
      ["rule" .= rule,"ruleVersion" .= (1 :: Int),"inputs" .= map identifier inputs
      ,"premises" .= premises,"steps" .= map evidenceValue parents,"unavailable" .= limitation]
    derivation (Occurrence owner path _ evidence _ _) = object
      ["id" .= key owner path,"outputs" .= [key owner path]
      ,"inputs" .= map identifier (references evidence),"evidence" .= evidenceValue evidence]

-- A malformed trace is an adapter error, independent of semantic refusals.
validate :: Text -> Value -> Either Text ()
validate model trace = do
  unless (get "artifactDigest" trace == String (digest bytes)) (Left "target-trace-artifact-digest")
  unless (length ids == length (nub ids)) (Left "target-trace-duplicate-occurrence")
  unless (length checkedIds == length (nub checkedIds)) (Left "target-trace-duplicate-checked-occurrence")
  unless (length derivationIds == length (nub derivationIds)) (Left "target-trace-duplicate-derivation")
  forM_ checked $ \c -> unless (get "unavailable" c == Null && get "valueDigest" c /= Null)
    (Left "target-trace-unresolved-checked-occurrence")
  forM_ checked $ \c -> do
    let links = array (get "sourceLinks" c)
        locator = object ["owner" .= get "owner" c,"root" .= get "root" c,"path" .= get "path" c]
    unless ((get "sourcePrecision" c `elem` [String "exact",String "derived"]) == not (null links))
      (Left "source-trace-invalid-precision")
    forM_ links $ \link -> do
      unless (get "source" link `elem` sourceIds && get "checked" link == locator)
        (Left "source-trace-unresolved-alignment")
      unless (get "rule" link `elem` [String "source.direct-first-order",String "source.compiled-clause",String "source.explicit-signature"] && get "ruleVersion" link == Number 1)
        (Left "source-trace-unversioned-alignment")
      if get "rule" link == String "source.compiled-clause" then do
        unless (get "sourcePrecision" c == String "derived") (Left "source-trace-case-claimed-exact")
        case [get "value" r | r <- array (get "templateRoots" trace)
          , get "owner" r == get "owner" locator, get "root" r == get "root" locator] of
          [value] -> do
            validateClauseReplay value link
            validateClauseCoverage value (get "path" locator) links
          _ -> Left "source-trace-missing-replay-root"
        unless (any (\s -> get "id" s == get "source" link && get "role" s == String "clause")
          (array (get "sourceOccurrences" trace))) (Left "source-trace-case-without-clause")
        else pure ()
      if get "rule" link == String "source.explicit-signature" then
        unless (get "root" locator == String "type" && get "sourcePrecision" c == String "derived"
          && any (\s -> get "id" s == get "signature" link && get "role" s `elem` [String "function-signature",String "constructor-signature"]
            && get "owner" s == get "owner" locator) (array (get "sourceOccurrences" trace))
          && any (\s -> get "id" s == get "source" link && get "anchor" s == get "signature" link
            && get "owner" s == get "owner" locator) (array (get "sourceOccurrences" trace)))
          (Left "source-trace-invalid-signature")
        else pure ()
      whenTransported link
  forM_ targets $ \t -> do
    unless (get "derivation" t `elem` derivationIds) (Left "target-trace-unresolved-derivation")
    whenDerived t
    unless (length (array (get "intervals" t)) == 1) (Left "target-trace-missing-interval")
    forM_ (array (get "intervals" t)) $ \i -> case (offset (get "start" i),offset (get "end" i)) of
      (Just a,Just b) | 0 <= a && a < b && b <= BS.length bytes ->
        case TE.decodeUtf8' (BS.take (b-a) (BS.drop a bytes)) of
          Right _ -> Right ()
          Left _ -> Left "target-trace-invalid-utf8-interval"
      _ -> Left "target-trace-invalid-interval"
  forM_ derivations $ \d -> do
    unless (all (`elem` ids) (array (get "outputs" d))) (Left "target-trace-unresolved-output")
    unless (all (`elem` checkedIds) (array (get "inputs" d))) (Left "target-trace-unresolved-input")
    evidence (get "evidence" d)
  where
    bytes = TE.encodeUtf8 model
    targets = array (get "targetOccurrences" trace)
    checked = array (get "checkedOccurrences" trace)
    derivations = array (get "derivations" trace)
    ids = map (get "id") targets
    checkedIds = map (get "id") checked
    derivationIds = map (get "id") derivations
    sourceIds = map (get "id") (array (get "sourceOccurrences" trace))
    whenDerived t = case get "sourcePrecision" t of
      String "derived" -> case filter ((== get "derivation" t) . get "id") derivations of
        [d] -> unless (not (null (array (get "inputs" d)))
          && all (\ref -> any (\c -> get "id" c == ref && get "sourcePrecision" c `elem` [String "exact",String "derived"]) checked) (array (get "inputs" d))
          && noBoundary (get "evidence" d)) (Left "source-trace-promoted-unavailable")
        _ -> Left "source-trace-unresolved-derivation"
      _ -> Right ()
    noBoundary e = get "unavailable" e == Null && all noBoundary (array (get "steps" e))
    whenTransported link = case get "preparation" link of
      Null -> Right ()
      p -> do
        unless (get "rule" p `elem` [String "source.same-term-structure",String "source.same-signature-structure"]
          && get "ruleVersion" p == Number 1 && get "template" p == get "checked" link)
          (Left "source-trace-invalid-preparation")
        if get "rule" p == String "source.same-signature-structure" then do
          let ref = get "checked" link
              matches r = get "owner" r == get "owner" ref && get "root" r == get "root" ref
          case (filter matches (array (get "templateRoots" trace)),filter matches (array (get "checkedRoots" trace))) of
            ([before],[after]) -> unless (get "root" ref == String "type"
              && get "arguments" (get "preparation" after) == toJSON ([] :: [Value])
              && signatureShape (get "value" before) /= Nothing
              && signatureShape (get "value" before) == signatureShape (get "value" after))
                (Left "source-trace-invalid-signature-transport")
            _ -> Left "source-trace-missing-signature-root"
          else unless (get "root" (get "checked" link) == String "compiled") (Left "source-trace-invalid-preparation")
    rules = [(get "id" r,get "version" r) | r <- array (get "rules" trace)]
    evidence step = do
      unless ((get "rule" step,get "ruleVersion" step) `elem` rules) (Left "target-trace-unversioned-rule")
      unless (all (`elem` checkedIds) (array (get "inputs" step))) (Left "target-trace-unresolved-premise")
      mapM_ evidence (array (get "steps" step))
    offset (Number n) = toBoundedInteger n
    offset _ = Nothing
