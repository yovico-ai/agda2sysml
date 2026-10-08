{-# LANGUAGE OverloadedStrings, LambdaCase #-}
-- | A deliberately bounded bridge. Highlighting resolves uses, pattern origins
-- identify binders, and checked patterns drive case-tree replay. No spelling,
-- source-clause ordinal, or term digest establishes a correspondence.
module Agda2SysML.SourceAlignment (collect, Direct(..), Reference(..), matchTerm, Signature(..), matchSignature, matchConstructorSignature) where

import Agda.Compiler.Backend hiding (Direct, Signature)
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as N
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Common.Aspect as H
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Parser (parseFile, moduleParser)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base (ScopeInfo(..))
import qualified Agda.TypeChecking.CompiledClause as CC
import qualified Agda.Utils.RangeMap as RM
import qualified Agda2SysML.SourceCatalog as Catalog
import Control.Monad (unless, forM)
import Data.Aeson hiding (Options, pairs)
import qualified Data.Aeson.KeyMap as KM
import Data.Foldable (toList)
import Data.List (nub, sortOn)
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

type Binding = (Text, Int)
data Reference = Bound Binding | Global A.QName deriving (Eq, Show)
-- Application spines have one head and ordered, explicit arguments. Each node
-- retains its source catalog identity, including transparent parentheses.
data Direct = Direct Value Reference [Direct] | Parenthesized Value Direct deriving Show
-- Only explicit first-order telescopes over named types are admitted. A typed
-- source binder has a compiler-resolved site; anonymous arrows have none.
data Signature = Carrier Direct | Arrow Value ArgInfo (Maybe Binding) Signature Signature
  | SignatureAt Value Signature

type Environment = M.Map Binding Int
type Link = ([Value], Value)

get :: Key -> Value -> Value
get k (Object fs) = maybe Null id (KM.lookup k fs)
get _ _ = Null
array :: Value -> [Value]
array (Array xs) = toList xs
array _ = []
require :: Bool -> Text -> Either Text ()
require ok reason = unless ok (Left reason)
one :: Text -> [a] -> Either Text a
one _ [x] = Right x
one reason _ = Left reason

binding :: Range -> Maybe Binding
binding r = do
  p <- rStart r
  m <- rangeModule r
  pure (T.pack (prettyShow m), fromIntegral (posPos p))

-- The checked term itself must have the same resolved head, ordered explicit
-- spine, and binder indices. Hidden insertion, beta/eta, projection elimination,
-- literals, and higher-order uses are deliberately refused in this rule.
matchTerm :: Environment -> Direct -> I.Term -> Either Text [Link]
matchTerm = matchTermWith S.empty

-- Constructor signatures alone admit a single proper projection on a bound
-- receiver. The checked tree has no separate bare-receiver term: only the
-- whole prefix expression receives a link to the real postfix term.
matchTermWith :: S.Set A.QName -> Environment -> Direct -> I.Term -> Either Text [Link]
matchTermWith projections env = go []
  where
    go path (Parenthesized source e) t = ((path,source) :) <$> go path e t
    go path (Direct source (Global q) [receiver]) (I.Var i [I.Proj _ r]) = do
      require (q == r && S.member q projections) "source-signature-projection-unavailable"
      receiverMatches receiver i
      pure [(path,source)]
    go path (Direct source reference args) t = do
      es <- case (reference,t) of
        (Bound b,I.Var i es) -> do
          require (M.lookup b env == Just i && null args && null es) "source-binder-mismatch"
          pure es
        (Global q,I.Def r es) | q == r -> pure es
        (Global q,I.Con r _ es) | q == I.conName r -> pure es
        _ -> Left "source-term-mismatch"
      checked <- forM es $ \case
        I.Apply a | visible a -> Right (unArg a)
        _ -> Left "source-elaboration-unavailable"
      require (length args == length checked) "source-argument-alignment-unavailable"
      children <- sequence [go (path ++ [String "eliminations",toJSON i,String "argument",String "value"]) a b
        | (i,(a,b)) <- zip [0 :: Int ..] (zip args checked)]
      pure ((path,source) : concat children)
    receiverMatches (Parenthesized _ receiver) i = receiverMatches receiver i
    receiverMatches (Direct _ (Bound b) []) i =
      require (M.lookup b env == Just i) "source-signature-projection-binder-mismatch"
    receiverMatches _ _ = Left "source-signature-projection-receiver-unavailable"

-- Paths refer to type wrappers and terms, never inferred sort annotations.
-- Abs extends the de Bruijn environment; NoAbs leaves it unchanged. A source
-- use of an omitted binder consequently cannot match a checked variable.
matchSignature :: Signature -> I.Type -> Either Text [([Value],Value,Environment)]
matchSignature = matchConstructorSignature S.empty

matchConstructorSignature :: S.Set A.QName -> Signature -> I.Type -> Either Text [([Value],Value,Environment)]
matchConstructorSignature projections = go [] M.empty
  where
    emit path source env = (path,source,env)
    go path env (SignatureAt source sig) ty =
      (emit path source env :) <$> go path env sig ty
    go path env (Carrier source) (I.El _ term) = do
      require (case term of I.Def{} -> True; _ -> False) "source-signature-carrier-unavailable"
      links <- matchTermWith projections env source term
      let rootSource = case source of Direct x _ _ -> x; Parenthesized x _ -> x
      pure (emit path rootSource env : [emit (path ++ [String "term"] ++ suffix) src env | (suffix,src) <- links])
    go path env (Arrow source info binder domain codomain) (I.El _ term) = case term of
      I.Pi dom cod -> do
        require (visible info && visible dom && getModality info == defaultModality && getModality dom == defaultModality)
          "source-signature-modality-unavailable"
        require (case domain of Arrow{} -> False; SignatureAt _ d -> firstOrder d; _ -> True)
          "source-signature-higher-order-unavailable"
        left <- go (path ++ [String "term",String "domain",String "type"]) env domain (I.unDom dom)
        let next = case cod of
              I.Abs{} -> maybe id (\b -> M.insert b 0) binder (M.map (+1) env)
              I.NoAbs{} -> env
        right <- go (path ++ [String "term",String "codomain",String "body"]) next codomain (I.unAbs cod)
        pure (emit path source env : emit (path ++ [String "term"]) source env : left ++ right)
      _ -> Left "source-signature-arrow-mismatch"
    firstOrder (SignatureAt _ d) = firstOrder d
    firstOrder Carrier{} = True
    firstOrder _ = False

-- Catalog lookup is syntax-to-syntax, within the same parsed checked text.
-- It never joins source and checked terms by their coordinates.
occurrence :: Value -> Text -> Range -> Either Text Value
occurrence catalog role range = do
  require (rStart range /= Nothing) "source-range-unavailable"
  o <- one "source-occurrence-ambiguous" [o | o <- array (get "occurrences" catalog)
    , get "role" o == String role, get "navigation" o == Catalog.navigation range
    , get "rangeUnavailable" o == Null]
  pure (get "id" o)

collect :: (A.QName -> Text) -> [Definition] -> Interface -> RangeFile -> Value -> TCM Value
collect symbol registry iface file catalog = do
  ((parsed,_),_) <- runPM (parseFile moduleParser file (TL.unpack (iSource iface)))
  let groups = declarations (C.modDecls parsed)
      signatureGroups = signatureDeclarations (C.modDecls parsed)
      ownDefinitions = [d | d <- sortOn (symbol . defName) (HM.elems (_sigDefinitions (iSignature iface)))
        , Just (m,_) <- [binding (A.nameBindingSite (A.qnameName (defName d)))]
        , m == moduleName]
      functions = [d | d <- ownDefinitions, case theDef d of Function{} -> True; _ -> False]
      signatures = [d | d <- ownDefinitions, case theDef d of Function{} -> True; Constructor{} -> True; _ -> False]
      results = map alignDefinition functions
      signatureResults = map alignSignatureDefinition signatures
      alignSignatureDefinition d = report d $ do
        (role,r,n,ty) <- one "source-signature-anchor-unavailable" [(role,r,n,ty) | (nr,role,r,n,ty) <- signatureGroups
          , fmap (\p -> (moduleName,fromIntegral (posPos p))) (rStart nr)
              == binding (A.nameBindingSite (A.qnameName (defName d)))]
        resolved <- reference (C.QName n)
        require (resolved == Global (defName d)) "source-signature-owner-mismatch"
        require (role == case theDef d of Constructor{} -> "constructor-signature"; _ -> "function-signature")
          "source-signature-kind-mismatch"
        sid <- occurrence catalog role r
        sig <- typeExpression ty
        links <- (case theDef d of
          Constructor{} -> matchConstructorSignature properProjections
          _ -> matchSignature) sig (defType d)
        pure [object ["checked" .= object ["owner" .= symbol (defName d),"root" .= ("type" :: Text),"path" .= path]
          ,"source" .= src,"signature" .= sid,"bindings" .= bindingValues env
          ,"rule" .= ("source.explicit-signature" :: Text),"ruleVersion" .= (1 :: Int)]
          | (path,src,env) <- links]
      report d result = case result of
        Left reason -> object ["owner" .= symbol (defName d),"unavailable" .= (reason :: Text),"links" .= ([] :: [Value])]
        Right links -> object ["owner" .= symbol (defName d),"unavailable" .= Null,"links" .= (links :: [Value])]
      alignDefinition d = let
        result = do
          clauses <- one "source-anchor-unavailable" [cs | (r,cs) <- groups
            , fmap (\p -> (moduleName,fromIntegral (posPos p))) (rStart r)
                == binding (A.nameBindingSite (A.qnameName (defName d)))]
          alignFunction d clauses
        in case result of
          Left reason -> object ["owner" .= symbol (defName d),"unavailable" .= reason,"links" .= ([] :: [Value])]
          Right links -> object ["owner" .= symbol (defName d),"unavailable" .= Null,"links" .= links]
  pure $ object ["version" .= (1 :: Int),"rule" .= ("source.direct-first-order" :: Text)
    ,"ruleVersion" .= (1 :: Int),"definitions" .= results,"signatures" .= signatureResults]
  where
    moduleName = T.pack (prettyShow (iTopLevelModuleName iface))
    scope = iInsideScope iface
    sites = M.fromListWith (++) [(site,[defName d]) | d <- registry, not (defCopy d)
      , Just site <- [binding (A.nameBindingSite (A.qnameName (defName d)))]]
    properProjections = S.fromList [defName d | d <- registry
      , Function{funProjection = Right p} <- [theDef d]
      , Just _ <- [projProper p], projIndex p == 1
      , I.El _ (I.Pi dom _) <- [defType d]
      , visible dom, getModality dom == defaultModality]
    highlights = RM.toMap (iHighlighting iface)
    reference q = do
      require (not (C.isOperator (C.unqualify q))) "source-operator-alignment-unavailable"
      let r = getRange q
          spans = [(fromIntegral (posPos (iStart' i)),fromIntegral (posPos (iEnd' i))) | i <- rangeIntervals r]
          -- Every character of the identifier must have the same resolved
          -- binding evidence. Partial/overlapping highlighting cannot suffice.
          at p = maybe (Left "source-resolution-unavailable") Right (IM.lookup p highlights)
      aspects <- traverse at [p | (a,b) <- spans,p <- [a..b-1]]
      a <- one "source-resolution-ambiguous" (nub aspects)
      site <- maybe (Left "source-resolution-unavailable") Right (H.definitionSite a)
      let key = (T.pack (prettyShow (H.defSiteModule site)), H.defSitePos site)
      case H.aspect a of
        Just (H.Name (Just H.Bound) _) -> Right (Bound key)
        Just (H.Name _ _) -> Global <$> one "source-resolution-ambiguous" (nub (M.findWithDefault [] key sites))
        _ -> Left "source-resolution-unavailable"
    declarations ds = case fst $ N.runNice (N.NiceEnv False C.NoWhere_) $ N.niceDeclarations (_scopeFixities scope) ds of
      Left _ -> []
      Right nice -> concatMap visit nice
    visit = \case
      N.FunDef _ _ _ _ _ _ n cs -> [(getRange n,cs)]
      N.NiceModule _ _ _ _ _ _ ds -> declarations ds
      N.NiceMutual _ _ _ _ ds -> concatMap visit ds
      N.NiceOpaque _ _ ds -> concatMap visit ds
      N.NiceRecDef _ _ _ _ _ _ _ _ ds -> declarations ds
      _ -> []
    bindingValues env = [object ["module" .= m,"position" .= p,"index" .= n] | ((m,p),n) <- M.toAscList env]
    signatureDeclarations ds = case fst $ N.runNice (N.NiceEnv False C.NoWhere_) $ N.niceDeclarations (_scopeFixities scope) ds of
      Left _ -> []
      Right nice -> concatMap signatureVisit nice
    signatureVisit = \case
      N.FunSig r _ _ _ _ _ _ _ n ty -> [(getRange n,"function-signature",r,n,ty)]
      N.NiceModule _ _ _ _ _ _ ds -> signatureDeclarations ds
      N.NiceMutual _ _ _ _ ds -> concatMap signatureVisit ds
      N.NiceOpaque _ _ ds -> concatMap signatureVisit ds
      N.NiceRecDef _ _ _ _ _ _ _ _ ds -> signatureDeclarations ds
      N.NiceDataDef _ _ _ _ _ _ _ cs -> concatMap constructorSignature cs
      N.NiceLoneConstructor _ cs -> concatMap constructorSignature cs
      _ -> []
    constructorSignature (N.Axiom r _ _ _ _ n ty) = [(getRange n,"constructor-signature",r,n,ty)]
    constructorSignature _ = []
    typeExpression ty = case ty of
      -- Parser.Helpers.typeSig wraps every signature, including closed arrows.
      -- Unwrap syntax only: matchSignature still rejects added checked binders.
      C.Generalized x -> SignatureAt <$> occurrence catalog "generalized" (getRange ty) <*> typeExpression x
      C.Paren r x -> SignatureAt <$> occurrence catalog "parenthesized" r <*> typeExpression x
      C.Fun r a b -> Arrow <$> occurrence catalog "function-type" r <*> pure (argInfo a) <*> pure Nothing
        <*> typeExpression (unArg a) <*> typeExpression b
      C.Pi tel result -> do
        src <- occurrence catalog "dependent-function-type" (getRange ty)
        tailType <- typeExpression result
        groups <- traverse typedGroup (toList tel)
        pure (SignatureAt src (foldr (\(o,info,b,d) -> Arrow o info (Just b) d) tailType (concat groups)))
      _ -> Carrier <$> expression ty
    typedGroup (C.TBind r names ty) = do
      src <- occurrence catalog "typed-binding" r
      domain <- typeExpression ty
      forM (toList names) $ \arg -> do
        let b = namedThing (unArg arg)
            n = C.binderName b
        require (visible arg && C.binderPattern b == Nothing && not (C.bnameIsFinite n)
          && C.theTacticAttribute (C.bnameTactic n) == Nothing) "source-signature-binder-unavailable"
        ref <- reference (C.QName (C.boundName n))
        site <- case ref of Bound site -> Right site; _ -> Left "source-signature-binder-unavailable"
        -- Reparsed ranges have no rangeModule; the source is this exact interface.
        require (fmap (\p -> (moduleName,fromIntegral (posPos p))) (rStart (getRange (C.boundName n))) == Just site)
          "source-signature-binder-mismatch"
        pure (src,argInfo arg,site,domain)
    typedGroup _ = Left "source-signature-let-unavailable"
    expression e = case e of
      C.Paren r x -> Parenthesized <$> occurrence catalog "parenthesized" r <*> expression x
      C.Ident q -> Direct <$> occurrence catalog "identifier" (getRange q) <*> reference q <*> pure []
      C.RawApp r xs -> case toList xs of
        C.Ident q:args -> Direct <$> occurrence catalog "raw-application" r <*> reference q <*> traverse expression args
        _ -> Left "source-expression-unavailable"
      _ -> Left "source-expression-unavailable"
    patternSpine (C.ParenP _ p) = patternSpine p
    patternSpine (C.RawAppP _ ps) = case toList ps of
      C.IdentP _ q:args -> Right (q,args)
      _ -> Left "source-pattern-unavailable"
    patternSpine (C.IdentP _ q) = Right (q,[])
    patternSpine _ = Left "source-pattern-unavailable"
    patterns source checked = do
      require (length source == length checked && all visible checked) "source-implicit-pattern-unavailable"
      pairs <- concat <$> sequence [pattern s (namedThing (unArg c)) | (s,c) <- zip source checked]
      require (length pairs == length (nub (map fst pairs)) && length pairs == length (nub (map snd pairs))) "source-binder-ambiguous"
      pure pairs
    pattern source checked = do
      (q,args) <- patternSpine source
      ref <- reference q
      case (ref,checked) of
        (Bound b,I.VarP info v) -> do
          require (null args && null (I.patAsNames info)) "source-pattern-unavailable"
          case I.patOrigin info of
            I.PatOVar n -> require (binding (A.nameBindingSite n) == Just b) "source-binder-mismatch"
            _ -> Left "source-binder-origin-unavailable"
          pure [(b,I.dbPatVarIndex v)]
        (Global name,I.ConP c info ps) -> do
          require (name == I.conName c && I.patOrigin (I.conPInfo info) == I.PatOCon
            && null (I.patAsNames (I.conPInfo info))) "source-pattern-mismatch"
          patterns args ps
        _ -> Left "source-pattern-mismatch"
    sourceClause owner (N.Clause _ _ lhs rhs wh children) = do
      require (null children && null (C.lhsWithExpr lhs) && null (C.lhsRewriteEqn lhs)) "source-with-rewrite-unavailable"
      require (case wh of C.NoWhere -> True; _ -> False) "source-where-unavailable"
      (headName,ps) <- patternSpine (C.lhsOriginalPattern lhs)
      ref <- reference headName
      require (ref == Global owner) "source-owner-mismatch"
      e <- case rhs of C.RHS x -> expression x; _ -> Left "source-rhs-unavailable"
      cid <- occurrence catalog "clause" (getRange lhs `fuseRange` rhs `fuseRange` wh)
      pure (cid,ps,e)
    alignFunction d sourceClauses = case theDef d of
      Function {funClauses = checkedClauses,funCompiled = Just tree,funWith = Nothing,funProjection = Left _} -> do
        sources <- traverse (sourceClause (defName d)) sourceClauses
        require (length sources == length checkedClauses && not (null sources)) "source-clause-count-unavailable"
        -- First establish pattern origins AND RHS alignment. Only then require
        -- a bijection. Neither list position nor uniqueness supplies evidence.
        matched <- forM sources $ \(cid,ps,e) -> do
          let candidates = mapMaybe (\(index,cl) -> either (const Nothing) Just $ do
                require (I.clauseWhereModule cl == Nothing && I.clauseUnreachable cl /= Just True) "source-clause-transformation-unavailable"
                env <- M.fromList <$> patterns ps (I.namedClausePats cl)
                body <- maybe (Left "source-rhs-unavailable") Right (I.clauseBody cl)
                links <- matchTerm env e body
                pure (index,cl,env,links)) (zip [0 :: Int ..] checkedClauses)
          require (not (null candidates)) "source-alignment-unavailable"
          (index,cl,env,links) <- one "source-alignment-ambiguous" candidates
          pure (cid,index,cl,env,e,links)
        require (length (nub [i | (_,i,_,_,_,_) <- matched]) == length checkedClauses) "source-alignment-ambiguous"
        compiled <- replay [] [] [(c,I.namedClausePats cl) | c@(_,_,cl,_,_,_) <- matched] tree
        require (sortOn id [i | (_,_,i,_,_,_) <- compiled] == sortOn id [i | (_,i,_,_,_,_) <- matched])
          "source-compiled-clause-coverage-unavailable"
        let owner = symbol (defName d)
            emit rule root path cid index env certificate links = [object
              ["checked" .= object ["owner" .= owner,"root" .= (root :: Text),"path" .= (path ++ suffix)]
              ,"source" .= source,"clause" .= cid,"checkedClause" .= index
              ,"bindings" .= [object ["module" .= m,"position" .= p,"index" .= n] | ((m,p),n) <- M.toAscList env]
              ,"rule" .= (rule :: Text),"ruleVersion" .= (1 :: Int),"replay" .= certificate]
              | (suffix,source) <- links]
        pure $ concat [emit "source.direct-first-order" "clauses" [toJSON i,String "body"] cid i env Null links | (cid,i,_,env,_,links) <- matched]
          ++ concat [emit "source.direct-first-order" "compiled" (path ++ [String "body"]) cid i env Null links
            ++ concat [emit "source.compiled-clause" "compiled" node cid i env certificate [([],cid)]
              | node <- [] : [array (get "child" step) | step <- trail]]
            | (path,cid,i,env,links,(trail,slots)) <- compiled
            , let certificate = object ["leaf" .= path,"splits" .= trail,"binderPermutation" .= slots]]
      Function {funWith = Just _} -> Left "source-with-rewrite-unavailable"
      _ -> Left "source-function-transformation-unavailable"
    -- Replay constructor splits in their actual compiled order. A candidate's
    -- pattern spine is consumed at the split's argument position, never zipped
    -- with source order. Leaf slots give an explicit checked-index permutation.
    replay path trail candidates = \case
      CC.Done slots body -> do
        ((cid,index,_,originalEnv,e,_),ps) <- one "source-alignment-ambiguous" candidates
        require (length ps == length slots && all visible slots) "source-compiled-binders-unavailable"
        oldIndices <- forM ps $ \p -> case namedThing (unArg p) of
          I.VarP _ v -> Right (I.dbPatVarIndex v)
          _ -> Left "source-compiled-pattern-unavailable"
        require (length (nub oldIndices) == length oldIndices) "source-binder-ambiguous"
        let permutation = M.fromList (zip oldIndices (reverse [0..length slots-1]))
        env <- traverse (\old -> maybe (Left "source-compiled-binder-unavailable") Right (M.lookup old permutation)) originalEnv
        links <- matchTerm env e body
        pure [(path,cid,index,env,links,(trail,oldIndices))]
      CC.Case arg branches -> do
        require (not (CC.projPatterns branches) && not (CC.lazyMatch branches)
          && CC.fallThrough branches == Just False && null (CC.litBranches branches)
          && maybe True (const False) (CC.etaBranch branches)
          && maybe True (const False) (CC.catchallBranch branches)) "source-case-transformation-unavailable"
        let n = unArg arg
        concat <$> sequence [do
          selected <- forM candidates $ \(c,ps) -> case drop n ps of
            p:_ | n >= 0 -> case namedThing (unArg p) of
              I.ConP headName _ children -> pure
                [(c,take n ps ++ children ++ drop (n+1) ps) | I.conName headName == constructor,length children == arity]
              _ -> Left "source-overlapping-patterns-unavailable"
            _ -> Left "source-compiled-binders-unavailable"
          let child = path ++ [String "constructors",toJSON j,String "branch",String "tree"]
              step = object ["path" .= path,"argument" .= n,"constructor" .= symbol constructor
                ,"arity" .= arity,"branch" .= j,"child" .= child]
          replay child (trail ++ [step]) (concat selected) branch
          | (j,(constructor,CC.WithArity arity branch)) <- zip [0 :: Int ..] (M.toAscList (CC.conBranches branches))]
      CC.Fail _ -> Left "source-absurd-clause-unavailable"
