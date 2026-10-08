{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Agda2SysML.Workflow (options, run) where

import Agda2SysML.Merge (mergeRoots)
import Agda2SysML.SourceCatalog (attachOwners)
import Agda2SysML.Mapping
import qualified Agda2SysML.Inventory as I
import qualified Agda2SysML.Derivation as Derivation
import qualified Agda2SysML.Target as Target
import qualified Agda2SysML.Review as Review
import qualified Data.Text.IO as TIO
import qualified Data.Set as S
import Agda2SysML.Sharing (digest)
import Agda.Interaction.Library.Parse (parseLibFile, runP)
import Agda.Interaction.Library.Base (_libIncludes, _libName, _libDepends)
import Agda.Syntax.Common.Pretty (prettyShow)
import Control.Monad (forM, forM_, when, unless, filterM)
import Data.Aeson hiding (Options)
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString as BS
import Data.Foldable (toList)
import Data.List (sort, nub)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Options.Applicative hiding (command, value)
import qualified Options.Applicative as O
import System.Directory
import System.Environment (getExecutablePath, lookupEnv)
import System.Exit
import System.FilePath
import System.IO (hPutStrLn, stderr)
import System.IO.Temp (withTempDirectory)
import System.Process (proc, createProcess, waitForProcess, cwd, readProcessWithExitCode)

data Mode = Inspect | Generate Bool deriving Eq
data Options = Options Mode (Maybe FilePath) (Maybe FilePath) [Text] FilePath

options :: Parser Options
options = hsubparser
  (O.command "inspect" (info (opts (pure Inspect)) (progDesc "Check source and mapping; write inventory"))
  <> O.command "generate" (info (opts (Generate <$> switch (long "diagnostic" <> help "Retain an explicitly incomplete report")))
    (progDesc "Generate and validate a SysML model")))
  where opts mode = Options <$> mode <*> optional (strOption (long "mapping" <> metavar "FILE"
          <> help "Optional local modeling roles; mapping-only selects the legacy model profile"))
          <*> optional (strOption (long "library" <> metavar "FILE" <> help "Agda library for automatic declaration generation"))
          <*> many (T.pack <$> strOption (long "root" <> metavar "MODULE" <> help "Entry module; repeat for multiple roots"))
          <*> strOption (long "output" <> metavar "DIRECTORY")

fatal :: String -> IO a
fatal = ioError . userError

get :: Text -> Value -> Value
get k (Object o) = fromMaybe Null (KM.lookup (K.fromText k) o)
get _ _ = Null
array :: Value -> [Value]
array (Array a) = toList a
array _ = []
string :: Value -> Text
string (String s) = s
string _ = ""

extensions :: [String]
extensions = [".agda", ".lagda", ".lagda.md", ".lagda.rst", ".lagda.tex", ".lagda.org", ".lagda.typ"]

run :: Options -> IO ()
run (Options mode mappingPath libraryPath entryModules outputPath) = do
  output <- makeAbsolute outputPath
  existing <- doesPathExist output
  when existing $ fatal "output directory already exists"
  mappingFile <- traverse makeAbsolute mappingPath
  mappingBytes <- traverse BS.readFile mappingFile
  mapped <- traverse (\bytes -> parseMapping bytes >>= either fatal pure) mappingBytes
  let automatic = isJust libraryPath
  (m,descriptor) <- case (libraryPath,mapped,mappingFile) of
    (Nothing,Just configured,Just file) -> do
      unless (null entryModules) $ fatal "--root requires --library"
      pure (configured,takeDirectory file </> library configured)
    (Just file,annotation,origin) -> do
      when (null entryModules || length (nub entryModules) /= length entryModules) $
        fatal "--library requires distinct, nonempty --root modules"
      absolute <- canonicalizePath file
      case (annotation,origin) of
        (Just configured,Just path) -> do
          declared <- canonicalizePath (takeDirectory path </> library configured)
          unless (declared == absolute) $ fatal "mapping library conflicts with --library"
          unless (roots configured == entryModules && not (inventoryLibrary configured)) $
            fatal "automatic generation annotations must keep the requested roots and import-closure inventory"
          pure (configured {roots = entryModules},absolute)
        _ -> pure (Mapping 2 (T.pack (dropExtension (takeFileName absolute))) absolute entryModules False M.empty,absolute)
    _ -> fatal "provide --library with --root, or --mapping"
  libFile <- canonicalizePath descriptor
  unless (takeExtension libFile == ".agda-lib") $ fatal "project.agda-library must name an .agda-lib file"
  libraryBytes <- BS.readFile libFile
  gitBefore <- gitIdentity (takeDirectory libFile)
  (parsed, warnings) <- runP <$> parseLibFile libFile
  lib <- either (fatal . show) pure parsed
  forM_ warnings (hPutStrLn stderr . show)
  includes <- traverse canonicalizePath (_libIncludes lib)
  when (null includes) $ fatal "the selected library has no include directories"
  let libraryId = T.pack (prettyShow (_libName lib))
  sourceRoots <- forM (roots m) $ \root -> do
    files <- filterM doesFileExist [dir </> modulePath root ++ ext | dir <- includes, ext <- extensions]
    case nub files of
      [f] -> pure f
      [] -> fatal ("entry module not found: " ++ T.unpack root)
      _ -> fatal ("entry module has multiple source files: " ++ T.unpack root)
  extraFiles <- if inventoryLibrary m then concat <$> traverse sources includes else pure []
  createDirectoryIfMissing True (takeDirectory output)
  withTempDirectory (takeDirectory output) ".agda2sysml-stage" $ \stage -> do
    forM_ mappingBytes (BS.writeFile (stage </> "mapping.yaml"))
    executable <- getExecutablePath
    executableDigest <- digest <$> BS.readFile executable
    registry <- lookupEnv "AGDA2SYSML_LIBRARIES_FILE"
    let registryArgs = maybe [] (\p -> ["--library-file=" ++ p]) registry
        check remaining accumulated = case remaining of
          [] -> pure accumulated
          f:fs -> do
            let outfile = stage </> "checked.json"
            (_,_,_,process) <- createProcess (proc executable
              (["_agda", "--no-main", "--checked-inventory=" ++ outfile]
               ++ ["--project-mapping=" ++ (stage </> "mapping.yaml") | isJust mappingBytes]
               ++ registryArgs ++ [f])) {cwd = Just (takeDirectory libFile)}
            code <- waitForProcess process
            unless (code == ExitSuccess) $ fatal "agda-check-failed"
            v <- eitherDecodeFileStrict outfile >>= either fatal pure
            combined <- either (fatal . T.unpack) pure (mergeRoots accumulated v)
            let seen = map (string . get "name") (array (get "modules" v))
                covered path = any (\dir -> moduleFromFile dir path `elem` seen) includes
            check (filter (not . covered) fs) combined
    merged <- check (nub (sourceRoots ++ sort extraFiles)) Null
    checked <- either (fatal . T.unpack) pure (attachOwners merged)
    let resolutions = array (get "resolutions" checked)
        resolutionErrors = concatMap checkResolution resolutions
        inventory = case checked of
          Object fields -> Object (KM.insert "project" (String (projectName m)) $
            KM.insert "selectionProfile" (String (if automatic then "declarations" else "models")) $
            KM.insert "models" (modelMetadata m resolutions) $ KM.insert "library" (String libraryId) fields)
          _ -> checked
    unless (null resolutionErrors) $ fatal (T.unpack (T.intercalate "\n" resolutionErrors))
    prepared <- either (fatal . T.unpack) pure (I.prepare m inventory)
    checkingAssumptions <- either (fatal . T.unpack) pure (I.assumptions prepared)
    lexicalOwners <- either (fatal . T.unpack) pure (I.enclosures prepared)
    let qualifiedInventory = case inventory of
          Object fields -> Object (KM.insert "lexicalOwners" lexicalOwners (KM.insert "modelAssumptions" checkingAssumptions fields))
          _ -> inventory
    encodeFile (stage </> "inventory.json") qualifiedInventory
    let generated = Target.generate prepared
        problems = if mode == Inspect then [] else Target.diagnostics generated
        complete = mode == Inspect || Target.complete generated
        files = ["inventory.json", "diagnostics.json"] ++
          [f | mode /= Inspect, f <- ["model.sysml","correspondence.json","review.html"]]
    when (mode /= Inspect) $ do
      either (fatal . T.unpack) pure (Derivation.validate (Target.modelText generated)
        (get "sourceCorrespondence" (Target.correspondence generated)))
      TIO.writeFile (stage </> "model.sysml") (Target.modelText generated)
      encodeFile (stage </> "correspondence.json") (Target.correspondence generated)
      (_,_,_,validator) <- createProcess (proc "agda2sysml-validate" [stage </> "model.sysml"])
      validatorCode <- waitForProcess validator
      unless (validatorCode == ExitSuccess) $ fatal "target-validation-failed"
      TIO.writeFile (stage </> "review.html") (Review.render prepared generated)
    encodeFile (stage </> "diagnostics.json") $ object ["schemaVersion" .= (1 :: Int), "diagnostics" .= problems]
    hashes <- forM files $ \f -> do d <- digest <$> BS.readFile (stage </> f); pure (f,d)
    gitAfter <- gitIdentity (takeDirectory libFile)
    currentLibraryBytes <- BS.readFile libFile
    unless (libraryBytes == currentLibraryBytes) $ fatal "library descriptor changed during checking"
    encodeFile (stage </> "manifest.json") $ object
      ["schemaVersion" .= (1 :: Int), "tool" .= ("agda2sysml 0.1.0" :: Text)
      ,"generatorBinaryDigest" .= executableDigest
      ,"inputRepository" .= repositoryIdentity gitBefore gitAfter
      ,"library" .= object ["name" .= libraryId, "descriptorDigest" .= digest libraryBytes
        ,"dependencies" .= map prettyShow (_libDepends lib)]
      ,"agdaVersion" .= ("2.8.0" :: Text), "mappingDigest" .= fmap digest mappingBytes
      ,"mappingVersion" .= (if isJust mappingBytes then Just (mappingVersion m) else Nothing)
      ,"selectionProfile" .= (if automatic then "declarations" else "models" :: Text), "entryModules" .= roots m
      ,"inventoryScope" .= (if inventoryLibrary m then "library" else "roots" :: Text)
      ,"sources" .= I.sourceManifest prepared
      ,"modelAssumptions" .= checkingAssumptions
      ,"required" .= [object ["symbol" .= symbol, "kind" .= kind] | (symbol,kind) <- S.toAscList (I.required prepared)]
      ,"target" .= object ["language" .= ("SysML 2.0" :: Text), "validator" .= ("SysML Pilot 2026-03 / 0.58.0" :: Text)]
      ,"targetValidation" .= (if mode == Inspect then "not-requested" else "accepted" :: Text)
      ,"mode" .= (if mode == Inspect then "inspect" else "generate" :: Text), "complete" .= complete
      ,"artifacts" .= M.fromList hashes]
    -- Atomic directory creation reserves the destination without replacing a race winner.
    -- The manifest is installed last, only after every artifact was serialized.
    createDirectory output
    forM_ (files ++ ["manifest.json"]) $ \f -> renameFile (stage </> f) (output </> f)
    unless complete $ exitWith (ExitFailure 2)
  where
    modulePath = joinPath . map T.unpack . T.splitOn "."
    checkResolution r
      | get "outsideScope" r == Bool True = ["module-outside-scope: " <> string (get "module" r)]
      | get "valid" (get "validation" r) == Bool False = [string (get "message" (get "validation" r))]
      | otherwise = concatMap (\ref -> case array (get "candidates" ref) of
          [] -> ["unresolved-symbol: " <> string (get "reference" ref)]
          [_] -> []
          _ -> ["ambiguous-symbol: " <> string (get "reference" ref)]) (array (get "references" r))

moduleFromFile :: FilePath -> FilePath -> Text
moduleFromFile root file = T.intercalate "." $ map T.pack $ splitDirectories $ strip (makeRelative root file)
  where strip p = case filter (`isExtensionOf` p) extensions of
          e:_ -> take (length p - length e) p
          [] -> p

sources :: FilePath -> IO [FilePath]
sources dir = do
  entries <- sort <$> listDirectory dir
  concat <$> forM entries (\entry -> do
    let p = dir </> entry
    symlink <- pathIsSymbolicLink p
    directory <- doesDirectoryExist p
    if symlink then fatal ("library inventory cannot silently omit a symbolic link: " ++ p)
    else if directory then if entry `elem` [".git", "_build", "dist-newstyle"] then pure [] else sources p
    else pure [p | any (`isExtensionOf` p) extensions])

-- Do not serialize paths, remote URLs, filenames from status, or command output.
-- Absence of Git is distinct from a verified clean repository.
gitIdentity :: FilePath -> IO Value
gitIdentity directory = findExecutable "git" >>= \case
  Nothing -> pure (object ["status" .= ("git-unavailable" :: Text)])
  Just git -> do
    (code,revision,_) <- readProcessWithExitCode git ["-C",directory,"rev-parse","--verify","HEAD"] ""
    if code /= ExitSuccess then pure (object ["status" .= ("no-revision" :: Text)]) else do
      (statusCode,status,_) <- readProcessWithExitCode git
        ["-C",directory,"status","--porcelain=v1","--untracked-files=normal"] ""
      pure $ object ["status" .= (if statusCode == ExitSuccess then "available" else "status-unavailable" :: Text)
        ,"revision" .= T.strip (T.pack revision)
        ,"dirty" .= (statusCode /= ExitSuccess || not (null status))]

repositoryIdentity :: Value -> Value -> Value
repositoryIdentity before after = object
  ["before" .= before, "after" .= after, "metadataChangedDuringCheck" .= (before /= after)]

modelMetadata :: Mapping -> [Value] -> Value
modelMetadata mapping resolutions = toJSON $ M.mapWithKey describe (models mapping)
  where
    describe key model = let
      resolution = case filter ((== String key) . get "model") resolutions of r:_ -> r; [] -> Null
      checked = get "validation" resolution
      referencesByName = M.fromList [(string (get "reference" r),get "candidates" r)
        | r <- array (get "references" resolution)]
      ref name = object ["reference" .= name,"symbols" .= M.findWithDefault Null name referencesByName]
      selected (Binder name) = object ["binder" .= name]
      selected (Position position) = object ["position" .= position]
      transitionMetadata = case transition model of
        Function symbol command before result -> object
          ["encoding" .= ("function" :: Text),"entry" .= ref symbol
          ,"before" .= selected before,"command" .= fmap selected command
          ,"checkedBefore" .= get "before" checked,"checkedCommand" .= get "command" checked
          ,"result" .= case result of
            DirectState -> object ["state" .= ("return" :: Text)]
            Family family projection variants -> object ["family" .= ref family,"projection" .= ref projection
              ,"variants" .= [object ["constructor" .= ref c,"category" .= category] | (c,category) <- M.toAscList variants]]]
        Relation symbol before after -> object ["encoding" .= ("relation" :: Text),"entry" .= ref symbol
          ,"before" .= before,"after" .= after,"checkedBefore" .= get "before" checked,"checkedAfter" .= get "after" checked]
      in object ["title" .= title model,"module" .= modelModule model
        ,"state" .= (case state model of InferState -> object ["infer" .= True]; NamedState name -> ref name)
        ,"commands" .= fmap ref (commands model),"transition" .= transitionMetadata
        ,"invariants" .= [object ["predicate" .= ref name,"stateArgument" .= fmap selected selector]
          | Invariant name selector <- invariants model]
        ,"theorems" .= map ref (theorems model)]
