{-# LANGUAGE LambdaCase, OverloadedStrings, RecordWildCards, ImplicitParams, ConstraintKinds,
             ExistentialQuantification, FlexibleInstances, UndecidableInstances #-}
-- | A single serializer description has both a pure reference interpreter and
-- a sharing interpreter. Term expansion is delayed until after memo lookup.
module Agda2SysML.Encoding
  ( Cache, newCache, definitionValue, termValue, typeValue, telescopeValue, packedDefinition ) where

import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names (namesIn')
import Agda.Syntax.Literal
import Agda.Syntax.Position
import qualified Agda.TypeChecking.CompiledClause as CC
import qualified Agda2SysML.Source as Source
import qualified Agda2SysML.Sharing as Sharing
import Control.Exception (evaluate)
import Control.Monad.State.Strict (runState)
import Data.Aeson hiding (object, (.=))
import qualified Data.Aeson.KeyMap as KM
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.IORef
import System.Mem.StableName
import qualified Agda.Utils.Maybe.Strict as Strict

data Encoded = Raw Value | ObjectNode [(Key,Encoded)] | ArrayNode [Encoded]
  | TermNode Term | TypeNode Type | SortNode Sort | InfoNode ArgInfo

type Pair = (Key,Encoded)
class ToEncoded a where
  encoded :: a -> Encoded
instance {-# OVERLAPPABLE #-} ToJSON a => ToEncoded a where encoded = Raw . toJSON
instance ToEncoded Encoded where encoded = id
instance {-# OVERLAPPABLE #-} ToEncoded a => ToEncoded [a] where encoded = ArrayNode . map encoded
instance {-# OVERLAPPING #-} ToEncoded String where encoded = Raw . toJSON
instance ToEncoded a => ToEncoded (Maybe a) where
  encoded Nothing = Raw Null
  encoded (Just a) = encoded a

(.=) :: ToEncoded a => Key -> a -> Pair
key .= value = (key,encoded value)
infixr 8 .=
object :: [Pair] -> Encoded
object = ObjectNode
node :: T.Text -> [Pair] -> Encoded
node tag fields = object ("tag" .= tag : fields)

type WithSymbols = (?symbol :: QName -> T.Text)
name :: WithSymbols => QName -> T.Text
name = ?symbol

reference :: WithSymbols => Encoded -> Value
reference = \case
  Raw value -> value
  ObjectNode fields -> Object (KM.fromList [(k,reference v) | (k,v) <- fields])
  ArrayNode xs -> toJSON (map reference xs)
  TermNode t -> reference (termBody t)
  TypeNode t -> reference (typBody t)
  SortNode s -> reference (sortTermBody s)
  InfoNode i -> reference (infoBody i)

definitionValue :: (QName -> T.Text) -> Definition -> Value
definitionValue symbol d = let ?symbol = symbol in reference (definition d)
termValue :: (QName -> T.Text) -> Term -> Value
termValue symbol t = let ?symbol = symbol in reference (term t)
typeValue :: (QName -> T.Text) -> Type -> Value
typeValue symbol t = let ?symbol = symbol in reference (typ t)

telescopeValue :: (QName -> T.Text) -> Telescope -> [Value]
telescopeValue symbol tel = let ?symbol = symbol in map reference (telescope tel)

data Entry = forall a. Entry Int (StableName a) Value
newtype Cache = Cache (IORef (IM.IntMap [Entry]))
newCache :: IO Cache
newCache = Cache <$> newIORef IM.empty

-- A stable-name hash only selects a bucket. Equality of stable names, with a
-- separate tag for each serializer domain, establishes object identity.
memo :: Cache -> Int -> a -> IO Value -> IO Value
memo (Cache cache) tag input compute = do
  forced <- evaluate input
  identity <- makeStableName forced
  table <- readIORef cache
  let bucket = IM.findWithDefault [] (hashStableName identity) table
      matches = [value | Entry kind key value <- bucket, kind == tag, eqStableName key identity]
  case matches of
    value:_ -> pure value
    [] -> do
      value <- compute
      modifyIORef' cache (IM.insertWith (++) (hashStableName identity) [Entry tag identity value])
      pure value

packedDefinition :: (QName -> T.Text) -> Cache -> IORef Sharing.Nodes -> Definition -> IO Value
packedDefinition symbol cache nodes d = let ?symbol = symbol in case definition d of
  ObjectNode fields -> Object . KM.fromList <$> traverse (\(k,v) -> (k,) <$> packed cache nodes v) fields
  other -> packed cache nodes other

packed :: WithSymbols => Cache -> IORef Sharing.Nodes -> Encoded -> IO Value
packed cache nodes = \case
  Raw value -> save Sharing.intern value
  ObjectNode fields -> traverse (\(k,v) -> (k,) <$> packed cache nodes v) fields >>= save Sharing.internShallow . Object . KM.fromList
  ArrayNode xs -> traverse (packed cache nodes) xs >>= save Sharing.internShallow . Array . V.fromList
  TermNode t -> memo cache 0 t (packed cache nodes (termBody t))
  TypeNode t -> memo cache 1 t (packed cache nodes (typBody t))
  SortNode s -> memo cache 2 s (packed cache nodes (sortTermBody s))
  InfoNode i -> memo cache 3 i (packed cache nodes (infoBody i))
  where
    save operation value = atomicModifyIORef' nodes $ \table ->
      let (result,table') = runState (operation value) table in (table',result)

source :: Range -> Encoded
source = Raw . Source.location

info :: ArgInfo -> Encoded
info = InfoNode

infoBody :: ArgInfo -> Encoded
infoBody i = object ["hiding" .= (case getHiding i of NotHidden -> "explicit"; Hidden -> "hidden"; Instance{} -> "instance" :: T.Text)
  ,"relevance" .= (case getRelevance i of Relevant{} -> "relevant"; Irrelevant{} -> "irrelevant"; ShapeIrrelevant{} -> "shapeIrrelevant" :: T.Text)
  ,"quantity" .= (case getQuantity i of Quantity0{} -> "zero"; Quantity1{} -> "one"; Quantityω{} -> "unrestricted" :: T.Text)
  ,"modality" .= show (getModality i)]

arg :: (a -> Encoded) -> Arg a -> Encoded
arg f (Arg i a) = object ["info" .= info i, "value" .= f a]

abstraction :: (a -> Encoded) -> Abs a -> Encoded
abstraction f a = object ["name" .= argNameToString (absName a)
  , "binds" .= (case a of Abs{} -> True; NoAbs{} -> False), "body" .= f (unAbs a)]

domain :: (a -> Encoded) -> Dom a -> Encoded
domain f d = object ["info" .= info (domInfo d), "type" .= f (unDom d)]

typ :: Type -> Encoded
typ = TypeNode

typBody :: WithSymbols => Type -> Encoded
typBody (El s t) = object ["sort" .= sortTerm s, "term" .= term t]

term :: Term -> Encoded
term = TermNode

termBody :: WithSymbols => Term -> Encoded
termBody = \case
  Var i es -> node "variable" ["index" .= i, "eliminations" .= map elim es]
  Def q es -> node "definition" ["symbol" .= name q, "eliminations" .= map elim es]
  Con c _ es -> node "constructor" ["symbol" .= name (conName c), "eliminations" .= map elim es]
  Lam i b -> node "lambda" ["info" .= info i, "abstraction" .= abstraction term b]
  Pi d b -> node "pi" ["domain" .= domain typ d, "codomain" .= abstraction typ b]
  Lit l -> node "literal" ["literal" .= literal l]
  Sort s -> node "sort" ["sort" .= sortTerm s]
  Level l -> node "level" ["level" .= level l]
  MetaV m es -> node "meta" ["identity" .= show m, "eliminations" .= map elim es]
  DontCare t -> node "irrelevant" ["term" .= term t]
  Dummy why es -> node "dummy" ["reason" .= why, "eliminations" .= map elim es]

elim :: WithSymbols => Elim -> Encoded
elim = \case
  Apply a -> node "apply" ["argument" .= arg term a]
  Proj _ q -> node "project" ["symbol" .= name q]
  IApply x y r -> node "intervalApply" ["left" .= term x, "right" .= term y, "interval" .= term r]

level :: WithSymbols => Level -> Encoded
level (Max n ps) = object ["constant" .= n, "maximum" .= map plus ps]
  where plus (Plus k t) = object ["offset" .= k, "term" .= term t]

sortTerm :: Sort -> Encoded
sortTerm = SortNode

sortTermBody :: WithSymbols => Sort -> Encoded
sortTermBody = \case
  Univ u l -> node "universe" ["kind" .= show u, "level" .= level l]
  Inf u n -> node "infiniteUniverse" ["kind" .= show u, "level" .= n]
  SizeUniv -> node "sizeUniverse" []
  LockUniv -> node "lockUniverse" []
  LevelUniv -> node "levelUniverse" []
  IntervalUniv -> node "intervalUniverse" []
  PiSort d a b -> node "piSort" ["domain" .= domain term d, "from" .= sortTerm a, "to" .= abstraction sortTerm b]
  FunSort a b -> node "functionSort" ["from" .= sortTerm a, "to" .= sortTerm b]
  UnivSort s -> node "universeSort" ["sort" .= sortTerm s]
  MetaS m es -> node "metaSort" ["identity" .= show m, "eliminations" .= map elim es]
  DefS q es -> node "definedSort" ["symbol" .= name q, "eliminations" .= map elim es]
  DummyS why -> node "dummySort" ["reason" .= why]

literal :: WithSymbols => Literal -> Encoded
literal = \case
  LitNat n -> node "natural" ["value" .= n]
  LitWord64 n -> node "word64" ["value" .= n]
  LitFloat n -> node "float64" ["value" .= show n]
  LitString s -> node "string" ["value" .= s]
  LitChar c -> node "character" ["value" .= [c]]
  LitQName q -> node "qualifiedName" ["symbol" .= name q]
  LitMeta m i -> node "metaLiteral" ["module" .= prettyShow m, "identity" .= show i]

patternTerm :: WithSymbols => DeBruijnPattern -> Encoded
patternTerm = \case
  VarP i v -> node "variable" ["index" .= dbPatVarIndex v, "name" .= argNameToString (dbPatVarName v)
    ,"absurd" .= (case patOrigin i of PatOAbsurd -> True; _ -> False)]
  DotP _ t -> node "dot" ["term" .= term t]
  ConP c _ ps -> node "constructor" ["symbol" .= name (conName c), "arguments" .= pats ps]
  LitP _ l -> node "literal" ["literal" .= literal l]
  ProjP _ q -> node "project" ["symbol" .= name q]
  IApplyP _ x y v -> node "interval" ["left" .= term x, "right" .= term y, "index" .= dbPatVarIndex v]
  DefP _ q ps -> node "definition" ["symbol" .= name q, "arguments" .= pats ps]
  where pats = map (arg (patternTerm . namedThing))

telescope :: WithSymbols => Telescope -> [Encoded]
telescope EmptyTel = []
telescope (ExtendTel d b) = object ["name" .= argNameToString (absName b), "domain" .= domain typ d] : telescope (unAbs b)

clause :: WithSymbols => Clause -> Encoded
clause Clause{..} = object
  ["source" .= source clauseFullRange, "whereModule" .= fmap prettyShow clauseWhereModule
  ,"telescope" .= telescope clauseTel
  ,"patterns" .= map (arg (patternTerm . namedThing)) namedClausePats
  ,"body" .= fmap term clauseBody, "type" .= fmap (arg typ) clauseType
  ,"recursive" .= clauseRecursive, "unreachable" .= clauseUnreachable]

definition :: WithSymbols => Definition -> Encoded
definition d = object $ ["name" .= name (defName d), "displayName" .= prettyShow (qnameToConcrete (defName d))
  ,"compilerIdentity" .= show (nameId (qnameName (defName d))), "moduleInstanceCopy" .= defCopy d
  ,"module" .= prettyShow (qnameModule (defName d))
  ,"abstract" .= (defAbstract d == AbstractDef)
  ,"bindingModule" .= (case rStart (nameBindingSite (qnameName (defName d))) of
      Just position -> case srcFile position of Strict.Just file -> fmap prettyShow (rangeFileName file); _ -> Nothing
      _ -> Nothing)
  ,"moduleIdentity" .= map (show . nameId) (mnameToList (qnameModule (defName d)))
  ,"whereModules" .= [map (show . nameId) (mnameToList m) | cl <- defClauses d, Just m <- [clauseWhereModule cl]]
  ,"type" .= typ (defType d), "source" .= source (nameBindingSite (qnameName (defName d)))
  ,"clauses" .= map clause (defClauses d)
  ,"statementDependencies" .= dependencies (defType d)
  ,"bodyDependencies" .= dependencies (defClauses d)] ++ kind (theDef d)
  where
    dependencies x = S.toAscList (namesIn' (S.singleton . name) x)
    kind = \case
      AbstractDefn x -> "abstract" .= True : kind x
      Function{..} -> ["kind" .= ("function" :: T.Text), "terminates" .= funTerminates
        ,"compiled" .= fmap caseTree funCompiled, "withParent" .= fmap name funWith
        ,"extendedLambda" .= maybe False (const True) funExtLam
        ,"mutual" .= fmap (map name) funMutual
        ,"opaque" .= (case funOpaque of TransparentDef -> False; _ -> True)
        ,"projection" .= (case funProjection of
            Left _ -> Raw Null
            Right p -> object ["proper" .= fmap name (projProper p)
              , "original" .= name (projOrig p), "index" .= projIndex p])]
      Datatype{..} -> ["kind" .= ("datatype" :: T.Text), "parameters" .= dataPars, "constructors" .= map name dataCons
        ,"moduleAlias" .= fmap clause dataClause
        -- Agda's Datatype alternative is inductive. Coinduction is recorded
        -- separately on Record; there is no coinductive Datatype alternative.
        ,"induction" .= ("Inductive" :: T.Text)]
      Record{..} -> ["kind" .= ("record" :: T.Text), "parameters" .= recPars
        ,"moduleAlias" .= fmap clause recClause
        ,"constructor" .= name (conName recConHead), "fields" .= map (name . unDom) recFields
        ,"induction" .= show recInduction, "etaEquality" .= show recEtaEquality']
      Constructor{..} -> ["kind" .= ("constructor" :: T.Text), "family" .= name conData, "parameters" .= conPars]
      Axiom{} -> ["kind" .= ("axiom" :: T.Text)]
      Primitive{..} -> ["kind" .= ("primitive" :: T.Text), "primitive" .= show primName]
      PrimitiveSort{} -> ["kind" .= ("primitiveSort" :: T.Text)]
      GeneralizableVar{} -> ["kind" .= ("generalizable" :: T.Text)]
      DataOrRecSig{} -> ["kind" .= ("signature" :: T.Text)]

caseTree :: WithSymbols => CC.CompiledClauses -> Encoded
caseTree = \case
  CC.Done xs body -> node "done" ["binders" .= map (arg (Raw . toJSON . argNameToString)) xs, "body" .= term body]
  CC.Fail xs -> node "absurd" ["binders" .= map (arg (Raw . toJSON . argNameToString)) xs]
  CC.Case index branches -> node "case"
    ["argument" .= arg (Raw . toJSON) index, "copattern" .= CC.projPatterns branches
    ,"constructors" .= [object ["symbol" .= name c,"branch" .= subtree b] | (c,b) <- M.toAscList (CC.conBranches branches)]
    ,"literals" .= [object ["literal" .= literal l,"branch" .= caseTree b] | (l,b) <- M.toAscList (CC.litBranches branches)]
    ,"eta" .= fmap (\(c,b) -> object ["constructor" .= name (conName c),"fields" .= map (name . unArg) (conFields c),"branch" .= subtree b]) (CC.etaBranch branches)
    ,"catchall" .= fmap caseTree (CC.catchallBranch branches), "fallThrough" .= CC.fallThrough branches
    ,"lazy" .= CC.lazyMatch branches]
  where subtree (CC.WithArity n b) = object ["arity" .= n, "tree" .= caseTree b]
