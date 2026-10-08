{-# LANGUAGE LambdaCase, OverloadedStrings, RecordWildCards, ImplicitParams, ConstraintKinds #-}
-- | Adapter for the pinned Agda API. No treeless compilation or proof erasure.
module Agda2SysML.Compiler (backend, term, typ) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad (unless, when, forM_)
import Control.Monad.Except (catchError)
import Data.Aeson hiding (Options)
import qualified Data.Map.Strict as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Agda.Compiler.Backend hiding (Args, reduced)
import Agda.Interaction.Options (OptDescr(..), ArgDescr(..), optSafe, optTerminationCheck, optPositivityCheck, optUniverseCheck, optWithoutK)
import Agda.Interaction.BasicOps (parseName)
import Agda.Interaction.Library.Base (pragmaStrings, _libName, _libIncludes)
import Agda.Interaction.Library (getAgdaLibFile, getPrimitiveLibDir, classifyBuiltinModule_)
import Agda.Utils.FileName (filePath)
import Agda.Syntax.Scope.Base (scopeLookup, anameName, _scopeCurrent, _scopeModules)
import Agda.Syntax.Common hiding (named)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Telescope (telView)
import Agda.TypeChecking.Substitute (TelV(..), raise, piApply, absApp)
import Agda.TypeChecking.Reduce (reduce, instantiateFull)
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Constraints (reallyNoConstraints)
import Agda.TypeChecking.MetaVars (newArgsMeta, newValueMeta)
import Agda.TypeChecking.Implicit (implicitArgs)
import Agda.TypeChecking.Free (freeVars)
import Agda.TypeChecking.Errors (prettyError)
import qualified Data.IntSet as IS
import qualified Agda2SysML.Sharing as Sharing
import qualified Agda2SysML.Source as Source
import qualified Agda2SysML.SourceCatalog as SourceCatalog
import qualified Agda2SysML.SourceAlignment as SourceAlignment
import qualified Agda2SysML.Encoding as Encoding
import System.Environment (lookupEnv)
import Data.IORef
import qualified Data.Set as S
import qualified Data.Aeson.KeyMap as KM
import System.FilePath (makeRelative, takeDirectory, isRelative, splitDirectories, takeFileName)
import qualified Agda2SysML.Mapping as Mapping
import Data.List (nub, sortOn)
import Data.Foldable (toList)
import System.IO (hPutStrLn, stderr)
import System.Directory (canonicalizePath)

backend :: Backend
backend = Backend Backend'
  { backendName = "agda2sysml", backendVersion = Just "0.1.0"
  , options = (Nothing, Nothing) :: (Maybe FilePath, Maybe FilePath)
  , commandLineFlags = [Option [] ["checked-inventory"]
      (ReqArg (\p (_, m) -> pure (Just p, m)) "FILE") "Write checked declarations"
    ,Option [] ["project-mapping"]
      (ReqArg (\p (o, _) -> pure (o, Just p)) "FILE") "Resolve project references"]
  , isEnabled = maybe False (const True) . fst
  , preCompile = \(o,m) -> do
      parsed <- liftIO $ traverse (\p -> Mapping.readMapping p >>= either (ioError . userError) pure) m
      nodes <- liftIO (newIORef Sharing.emptyNodes)
      cache <- liftIO Encoding.newCache
      verifyEncoding <- liftIO $ (== Just "1") <$> lookupEnv "AGDA2SYSML_VERIFY_ENCODING"
      own <- getSignature
      imported <- useTC stImports
      let allDefinitions = HM.elems (_sigDefinitions own) ++ HM.elems (_sigDefinitions imported)
          identities = M.fromList [(defName d,declaredName (defName d) <> "#" <>
            T.pack (show (nameId (qnameName (defName d))))) | d <- allDefinitions]
      pure (o,parsed,nodes,identities,cache,verifyEncoding,M.fromList [(nameId (qnameName (defName d)),d) | d <- allDefinitions])
  , postCompile = \(out,mapping,nodes,identities,cache,verifyEncoding,definitions) _ mods -> let ?identities = identities in case out of
      Nothing -> pure ()
      Just p -> do
        visited <- getVisitedModules
        let interfaces = map miInterface (M.elems visited)
            scopes = M.fromList [(prettyShow mn,(mn,si)) | i <- interfaces
              ,let si = iInsideScope i, mn <- M.keys (_scopeModules si)]
        resolved <- case mapping of
          Nothing -> pure []
          Just m -> sequence [case M.lookup (T.unpack (Mapping.modelModule model)) scopes of
            Nothing -> pure $ object ["model" .= k, "module" .= Mapping.modelModule model, "outsideScope" .= True]
            Just (mn,si) -> do
              selected <- sequence [do
                concrete <- parseName noRange (T.unpack ref)
                let candidates = nub $ map anameName $ scopeLookup concrete (si {_scopeCurrent = mn})
                pure (ref,candidates)
                | ref <- Mapping.references model]
              validation <- if all ((== 1) . length . snd) selected
                then validateModel (Mapping.mappingVersion m) model (M.fromList [(r,q) | (r,[q]) <- selected])
                else pure Null
              pure $ object ["model" .= k, "module" .= Mapping.modelModule model
                ,"references" .= [object ["reference" .= r, "candidates" .= map name qs] | (r,qs) <- selected]
                ,"validation" .= validation]
            | (k,model) <- M.toList (Mapping.models m)]
        intrinsicNames <- sequence [do q <- getBuiltinName' builtin; pure (key,fmap name q)
          | (key,builtin) <- [("bool",builtinBool),("true",builtinTrue),("false",builtinFalse)
            ,("equality",builtinEquality)
            ,("nat",builtinNat),("zero",builtinZero),("suc",builtinSuc)
            ,("list",builtinList),("nil",builtinNil),("cons",builtinCons)
            ,("level",builtinLevel),("levelUniverse",builtinLevelUniv),("levelZero",builtinLevelZero),("levelSuc",builtinLevelSuc),("levelMax",builtinLevelMax)]]
        completedModules <- completeSignatures nodes cache verifyEncoding
          (M.fromList [(name (defName d),d) | d <- M.elems definitions]) (M.elems mods)
        table <- liftIO (readIORef nodes)
        liftIO $ encodeFile p $ object
          ["schemaVersion" .= (1 :: Int), "agdaVersion" .= ("2.8.0" :: T.Text)
          ,"modules" .= completedModules, "resolutions" .= resolved, "nodes" .= table
          ,"builtins" .= M.fromList (intrinsicNames :: [(T.Text,Maybe T.Text)])
          ,"checking" .= [object ["module" .= prettyShow (iModuleName i)
            ,"pragmas" .= concatMap pragmaStrings (iDefaultPragmaOptions i ++ iFilePragmaOptions i)
            ,"safe" .= optSafe (iOptionsUsed i)
            ,"terminationCheck" .= optTerminationCheck (iOptionsUsed i)
            ,"positivityCheck" .= optPositivityCheck (iOptionsUsed i)
            ,"universeCheck" .= optUniverseCheck (iOptionsUsed i)
            ,"withoutK" .= optWithoutK (iOptionsUsed i)
            ,"imports" .= map (prettyShow . fst) (iImportedModules i)] | i <- interfaces]]
  , preModule = \_ _ m _ -> do
      liftIO $ hPutStrLn stderr ("Inventory " ++ prettyShow m)
      pure (Recompile ())
  , postModule = \(_,_,nodes,identities,_,_,definitions) _ _ m ds -> let ?identities = identities in do
      visited <- getVisitedModules
      files <- useTC stModuleToSourceId
      case (M.lookup m visited, M.lookup m files) of
        (Just mi,Just sf) -> do
          sourcePath <- srcFilePath sf
          primitiveDir <- liftIO getPrimitiveLibDir
          let path = filePath sourcePath
              isBuiltin = case classifyBuiltinModule_ primitiveDir sourcePath of Just _ -> True; Nothing -> False
          (syntax,sourceNodes) <- Source.sourceInfo (iInsideScope (miInterface mi)) (mkRangeFile sourcePath Nothing) (TL.unpack (iSource (miInterface mi)))
          let catalog = SourceCatalog.catalog (T.pack (prettyShow m)) (TL.toStrict (iSource (miInterface mi))) sourceNodes
          alignment <- SourceAlignment.collect name (M.elems definitions) (miInterface mi) (mkRangeFile sourcePath Nothing) catalog
          shared <- liftIO (readIORef nodes)
          let syntaxFunctions = case syntax of
                Object o -> case KM.lookup "functions" o of Just (Array xs) -> toList xs; _ -> []
                _ -> []
              origins fields
                | KM.lookup "bindingModule" fields /= Just (String (T.pack (prettyShow m))) = []
                | otherwise = case KM.lookup "source" fields >>= either (const Nothing) Just . Sharing.expand shared of
                    Just bindingSpan -> [entry | entry@(Object o) <- syntaxFunctions, KM.lookup "binding" o == Just bindingSpan]
                    Nothing -> []
          libs <- libToTCM (getAgdaLibFile (takeDirectory path))
          libraryRoots <- liftIO $ sequence [do dir' <- canonicalizePath dir; pure (T.pack (prettyShow (_libName l)),i,dir')
            | l <- libs, (i,dir) <- zip [0 :: Int ..] (_libIncludes l)]
          let owners = [(libraryName,i,localPath)
                | (libraryName,i,dir) <- libraryRoots
                ,let localPath = makeRelative dir path
                ,isRelative localPath, not (".." `elem` splitDirectories localPath)]
              (lib,root,relative) = case owners of
                owner:_ -> owner
                [] -> if isBuiltin then ("agda-2.8.0",0,makeRelative (filePath primitiveDir) path)
                  else ("unregistered",0,takeFileName path)
              origin = object ["library" .= lib, "root" .= root, "path" .= relative]
              attach (Object fields) = Object $ KM.insert "sourceSyntax" (toJSON (origins fields)) $ KM.insert "sourceModule" (String (T.pack (prettyShow m))) $
                KM.insert "id" (String (lib <> ":" <> case KM.lookup "name" fields of Just (String n) -> n; _ -> "")) fields
              attach v = v
          pure $ object ["name" .= prettyShow m, "definitions" .= map attach ds
            ,"source" .= origin, "sourceText" .= iSource (miInterface mi), "sourceSyntax" .= syntax
            ,"sourceAlignment" .= alignment,"sourceCorrespondence" .= catalog]
        _ -> genericError "compiler inventory is missing a checked module or source file"
  , compileDef = \(_,_,nodes,identities,cache,verifyEncoding,_) _ _ d -> let ?identities = identities in do
      packed <- liftIO (Encoding.packedDefinition name cache nodes d)
      when verifyEncoding $ do
        table <- liftIO (readIORef nodes)
        unless (Sharing.expand table packed == Right (Encoding.definitionValue name d)) $
          genericError "shared-encoding-mismatch"
      pure packed
  , scopeCheckingSuffices = False, mayEraseType = const (pure False)
  , backendInteractTop = Nothing, backendInteractHole = Nothing
  }

-- Imported signatures may contain generated helpers absent from the backend's
-- per-module traversal. Retain every such helper referenced by inventoried terms.
completeSignatures :: WithIdentities => IORef Sharing.Nodes -> Encoding.Cache -> Bool
  -> M.Map T.Text Definition -> [Value] -> TCM [Value]
completeSignatures nodes cache verifyEncoding registry modules = do
  let emitted = [d | md <- modules, d <- values (get "definitions" md)]
      initial = S.fromList (map (textOf . get "name") emitted)
  extras <- close initial emitted []
  pure [case md of
    Object fields -> Object (KM.insert "definitions" (toJSON
      (values (get "definitions" md) ++ [d | (owner,d) <- reverse extras, owner == textOf (get "name" md)])) fields)
    _ -> md | md <- modules]
  where
    get key (Object fields) = maybe Null id (KM.lookup key fields)
    get _ _ = Null
    textOf (String txt) = txt
    textOf _ = ""
    values (Array xs) = toList xs
    values _ = []
    dependencies d = do
      table <- liftIO (readIORef nodes)
      expanded <- traverse (either genericError pure . Sharing.expand table . (`get` d))
        ["statementDependencies","bodyDependencies","constructors","fields","constructor"]
      pure [textOf v | fieldValue <- expanded, v <- case fieldValue of String _ -> [fieldValue]; _ -> values fieldValue]
    close _ [] extras = pure extras
    close seen (d:rest) extras = do
      references <- dependencies d
      let missing = S.toAscList (S.fromList references S.\\ seen)
      additions <- traverse support missing
      close (S.union seen (S.fromList missing)) (map snd additions ++ rest) (additions ++ extras)
    support symbol = do
      def <- maybe (genericError ("missing-checked-signature: " ++ T.unpack symbol)) pure (M.lookup symbol registry)
      let definingModule = T.pack (prettyShow (qnameModule (defName def)))
          candidates = [md | md <- modules, let owner = textOf (get "name" md)
            ,owner == definingModule || (owner <> ".") `T.isPrefixOf` definingModule]
      owner <- case reverse (sortOn (T.length . textOf . get "name") candidates) of
        md:_ -> pure md
        [] -> genericError ("missing-generated-origin: " ++ T.unpack symbol)
      packed <- liftIO (Encoding.packedDefinition name cache nodes def)
      when verifyEncoding $ do
        table <- liftIO (readIORef nodes)
        unless (Sharing.expand table packed == Right (Encoding.definitionValue name def)) $
          genericError "shared-encoding-mismatch"
      let moduleName = textOf (get "name" owner)
          libraryName = textOf (get "library" (get "source" owner))
          located = case packed of
            Object fields -> Object $ KM.insert "id" (String (libraryName <> ":" <> symbol)) $
              KM.insert "sourceModule" (String moduleName) $
              KM.insert "generatedSupport" (Bool True) $
              KM.insert "sourceSyntax" (toJSON ([] :: [Value])) $
              KM.insert "origin" (object ["kind" .= ("checked-signature-support" :: T.Text), "module" .= moduleName]) fields
            _ -> packed
      pure (moduleName,located)

-- | Validation takes place in Agda's dependent context, using conversion, not
-- pretty-printed types or arity. Fresh inference metavariables never escape.
type WithIdentities = (?identities :: M.Map QName T.Text)

validateModel :: WithIdentities => Int -> Mapping.Model -> M.Map T.Text QName -> TCM Value
validateModel version model resolved = localTCState $
  catchError (reallyNoConstraints validate) $ \e -> do
    message <- prettyError e
    pure $ object ["valid" .= False, "message" .= prettyShow message]
  where
    require condition message = unless condition (genericError message)
    ref r = maybe (genericError "unresolved-symbol") pure (M.lookup r resolved)
    declaration r = ref r >>= (ignoreAbstractMode . getConstInfo)
    named r actual = do
      d <- declaration r
      args <- newArgsMeta (defType d)
      kind <- reduce (piApply (defType d) args)
      case unEl kind of
        Sort s -> equalType (El s (Def (defName d) (map Apply args))) actual
        _ -> genericError "incompatible-role: selected state or command is not a type"
    selected offset sel tel = do
      let allBinders = zip [0..] (binders tel)
          explicit = [(i,b) | (i,b@(_,dom)) <- drop offset allBinders, visible dom]
          matches = case sel of
            Mapping.Position pos -> take 1 (drop pos explicit)
            Mapping.Binder n -> [(i,b) | (i,b@(nm,_)) <- explicit, T.pack (argNameToString nm) == n]
      case matches of
        [(i,(_,dom))] -> pure (i,raise (length allBinders - i) (unDom dom))
        _ -> genericError "invalid-selector: expected a unique explicit telescope binder"
    checkState ty = do
      when (version == 1) $ require (IS.null (freeVars ty)) "unsupported-signature: version 1 requires a closed state type"
      case Mapping.state model of
        Mapping.InferState -> pure ()
        Mapping.NamedState r -> named r ty
    invariantState ty = case Mapping.state model of
      Mapping.NamedState r -> named r ty
      Mapping.InferState -> do
        (symbol,offset,selector) <- case Mapping.transition model of
          Mapping.Function symbol _ before _ -> pure (symbol,0,before)
          Mapping.Relation symbol before _ -> do
            d <- declaration symbol
            case theDef d of
              Datatype{dataPars = n} -> pure (symbol,n,Mapping.Position before)
              _ -> genericError "unsupported-encoding"
        d <- declaration symbol
        TelV tel _ <- telView (defType d)
        (i,_) <- selected offset selector tel
        (_,rest) <- inferPrefix i (defType d)
        reduced <- reduce rest
        case unEl reduced of
          Pi dom _ -> equalType ty (unDom dom)
          _ -> genericError "unsupported-signature: inferred state binder is unavailable"
    validate = do
      value <- case Mapping.transition model of
        Mapping.Function symbol command before result -> do
          d <- declaration symbol
          require (case theDef d of Function{} -> not (null (defClauses d)); _ -> False)
            "incompatible-role: transition must have an available checked function body"
          TelV tel codomain <- telView (defType d)
          addContext tel $ do
            (bi,stateType) <- selected 0 before tel
            checkState stateType
            ci <- case (command,Mapping.commands model) of
              (Just s,Just ty) -> do
                (i,t) <- selected 0 s tel
                require (i /= bi) "invalid-selector: command and before select the same binder"
                named ty t
                pure (Just i)
              _ -> pure Nothing
            projection <- case result of
              Mapping.DirectState -> equalType codomain stateType >> pure Null
              Mapping.Family family projectionName categories -> do
                -- Match the instantiated family, retaining all its indices.
                named family codomain
                familyDef <- declaration family
                actualConstructors <- case theDef familyDef of
                  Datatype{dataCons = cs} -> pure cs
                  _ -> genericError "incompatible-role: result family must be an inductive datatype"
                configured <- traverse ref (M.keys categories)
                require (length (nub configured) == length configured && all (`elem` configured) actualConstructors
                  && all (`elem` actualConstructors) configured) "incompatible-role: result variants must cover each constructor exactly once"
                p <- declaration projectionName
                require (not (null (defClauses p))) "incompatible-role: state projection must have a checked body"
                moduleParameters <- length . binders <$> lookupSection (qnameModule (defName p))
                addContext (ExtendTel (defaultDom codomain) (Abs "result" EmptyTel)) $ do
                  (contextArguments,remainingType) <- inferPrefix moduleParameters (defType p)
                  (implicit,rest) <- implicitArgs (-1) (/= NotHidden) remainingType
                  case unEl rest of
                    Pi dom out | visible dom -> do
                      equalType (unDom dom) (raise 1 codomain)
                      equalType (absApp out (Var 0 [])) (raise 1 stateType)
                      applied <- instantiateFull (Def (defName p) (map Apply (contextArguments ++ implicit ++ [Arg (domInfo dom) (Var 0 [])])))
                      pure (term applied)
                    _ -> genericError "unsupported-signature: projection must take exactly one explicit result argument"
            pure $ object ["valid" .= True, "encoding" .= ("function" :: T.Text)
              ,"symbol" .= name (defName d), "before" .= bi, "command" .= ci
              ,"telescope" .= telescope tel, "resultType" .= typ codomain, "stateType" .= typ stateType
              ,"projection" .= projection]
        Mapping.Relation symbol before after -> do
          d <- declaration symbol
          params <- case theDef d of
            Datatype{dataPars = n} -> pure n
            _ -> genericError "unsupported-encoding: relation must resolve to an inductive data family"
          TelV tel codomain <- telView (defType d)
          addContext tel $ do
            (bi,bty) <- selected params (Mapping.Position before) tel
            (ai,aty) <- selected params (Mapping.Position after) tel
            equalType bty aty
            checkState bty
            pure $ object ["valid" .= True, "encoding" .= ("relation" :: T.Text)
              ,"symbol" .= name (defName d), "before" .= bi, "after" .= ai
              ,"telescope" .= telescope tel, "resultType" .= typ codomain, "stateType" .= typ bty]
      -- Identity duplicates can arise through renaming even when spellings differ.
      invIds <- traverse (\(Mapping.Invariant n _) -> ref n) (Mapping.invariants model)
      theoremIds <- traverse ref (Mapping.theorems model)
      require (length invIds == length (nub invIds) && length theoremIds == length (nub theoremIds))
        "invalid-mapping: duplicate canonical contract selection"
      forM_ (Mapping.invariants model) $ \(Mapping.Invariant n selector) -> do
        d <- declaration n
        TelV tel codomain <- telView (defType d)
        addContext tel $ do
          let explicit = [b | b@(_,dom) <- binders tel, visible dom]
          s <- case selector of
            Just s -> pure s
            Nothing -> case explicit of
              [_] -> pure (Mapping.Position 0)
              _ -> genericError "unsupported-signature: invariant needs a state-argument selector"
          (_,ty) <- selected 0 s tel
          invariantState ty
          codomain' <- reduce codomain
          bool <- getBuiltinName' builtinBool
          require (case unEl codomain' of Sort{} -> True; Def q [] -> Just q == bool; _ -> False)
            "incompatible-role: invariant must return Bool or a proposition"
      require (not (containsMeta value)) "unsupported-signature: implicit parameters required by the output are not inferable"
      pure value

containsMeta :: Value -> Bool
containsMeta (Object fields) = KM.lookup "tag" fields `elem` map (Just . String) ["meta","metaSort","metaLiteral"]
  || any containsMeta (KM.elems fields)
containsMeta (Array xs) = any containsMeta (toList xs)
containsMeta _ = False

binders :: Telescope -> [(ArgName, Dom Type)]
binders EmptyTel = []
binders (ExtendTel dom b) = (absName b,dom) : binders (unAbs b)

-- Module parameters are explicit quantified context, not extra result inputs.
-- Their metavariables must all be solved by conversion against that context.
inferPrefix :: Int -> Type -> TCM (Args,Type)
inferPrefix 0 ty = pure ([],ty)
inferPrefix n ty = do
  reduced <- reduce ty
  case unEl reduced of
    Pi dom body -> do
      (_,v) <- newValueMeta RunMetaOccursCheck CmpEq (unDom dom)
      (args,result) <- inferPrefix (n - 1) (absApp body v)
      pure (Arg (domInfo dom) v : args,result)
    _ -> genericError "unsupported-signature: module telescope exceeds definition telescope"

name :: WithIdentities => QName -> T.Text
name q = M.findWithDefault ("unresolved#" <> T.pack (show (nameId (qnameName q)))) q ?identities

declaredName :: QName -> T.Text
declaredName q = T.intercalate "." (map component (mnameToList (qnameModule q) ++ [qnameName q]))
  where
    component n
      | isNoName n = "_#" <> T.pack (show (nameId n))
      | otherwise = T.replace "." "%2E" $ T.replace "#" "%23" $ T.replace "%" "%25" $
          T.pack (prettyShow (nameConcrete n))

typ :: WithIdentities => Type -> Value
typ = Encoding.typeValue name

term :: WithIdentities => Term -> Value
term = Encoding.termValue name

telescope :: WithIdentities => Telescope -> [Value]
telescope = Encoding.telescopeValue name
