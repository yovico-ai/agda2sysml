{-# LANGUAGE OverloadedStrings #-}
-- | Demand-driven definitional reduction of checked compiler terms. A bounded
-- reduction attempt returns Nothing when blocked; it never erases fields based
-- on relevance, names, or an assumption of proof irrelevance.
module Agda2SysML.Reduction (reduceHead, substituteTerms, shift, applyTerms, variable, freeVariables, canonicalTerm, rewriteTree) where

import Agda2SysML.Inventory
import Control.Monad (guard)
import Data.Aeson
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)

set :: Text -> Value -> Value -> Value
set k v (Object o) = Object (KM.insert (K.fromText k) v o)
set _ _ v = v
int :: Value -> Maybe Int
int (Number n) = toBoundedInteger n
int _ = Nothing
at :: Int -> [a] -> Maybe a
at n xs | n >= 0 = case drop n xs of x:_ -> Just x; _ -> Nothing
at _ _ = Nothing
variable :: Int -> Value
variable n = object ["tag" .= ("variable" :: Text),"index" .= n,"eliminations" .= ([] :: [Value])]
application :: Value -> Value
application x = object ["tag" .= ("apply" :: Text),"argument" .= object ["value" .= x]]
argument :: Value -> Maybe Value
argument e | get "tag" e == String "apply" = Just (get "value" (get "argument" e))
argument _ = Nothing

-- Both shifts and simultaneous substitutions respect Abs/NoAbs, including
-- abstractions embedded in dependent types. Replacement terms are raised when
-- transported under a binder.
walk :: (Int -> Int -> Value -> Value) -> Int -> Value -> Value
walk replace depth value@(Object fields)
  | get "tag" value == String "variable", Just i <- int (get "index" value) =
      replace depth i (set "eliminations" (toJSON (map (walk replace depth) (array (get "eliminations" value)))) value)
  | get "binds" value `elem` [Bool True,Bool False], get "body" value /= Null =
      Object (KM.mapWithKey (\k x -> walk replace (depth + if k == "body" && get "binds" value == Bool True then 1 else 0) x) fields)
  | otherwise = Object (fmap (walk replace depth) fields)
walk replace depth (Array xs) = Array (fmap (walk replace depth) xs)
walk _ _ value = value
shift :: Int -> Value -> Value
shift amount = walk (\depth i term -> if i < depth then term else set "index" (toJSON (i+amount)) term) 0
substituteTerms :: [Value] -> Value -> Maybe Value
substituteTerms replacements = subst 0
  where
    subst depth term@(Object fields)
      | get "tag" term == String "variable", Just i <- int (get "index" term) = do
          es <- traverse (subst depth) (array (get "eliminations" term))
          if i < depth then pure (set "eliminations" (toJSON es) term) else
            if i-depth < length replacements then do
              value <- at (i-depth) replacements
              applySpine (shift depth value) es
            else pure $ set "index" (toJSON (i-length replacements)) $ set "eliminations" (toJSON es) term
      | get "binds" term `elem` [Bool True,Bool False], get "body" term /= Null =
          Object <$> KM.traverseWithKey (\k x -> subst (depth + if k == "body" && get "binds" term == Bool True then 1 else 0) x) fields
      | otherwise = Object <$> traverse (subst depth) fields
    subst depth (Array xs) = Array <$> traverse (subst depth) xs
    subst _ value = Just value
applyTerms :: Value -> [Value] -> Maybe Value
applyTerms t = applySpine t . map application
applySpine :: Value -> [Value] -> Maybe Value
applySpine t [] = Just t
applySpine t (e:es) | get "tag" t == String "lambda" = do
  x <- argument e
  let binder = get "abstraction" t
  body <- if get "binds" binder == Bool True then substituteTerms [x] (get "body" binder) else Just (get "body" binder)
  applySpine body es
applySpine t es | get "tag" t `elem` map String ["variable","definition","constructor"] =
  Just (set "eliminations" (toJSON (array (get "eliminations" t) ++ es)) t)
applySpine _ _ = Nothing

-- Includes the exact declaration identities unfolded; callers retain these
-- as reduction premises alongside the unmodified source inventory.
reduceHead :: Inventory -> Value -> Maybe (Value,[Text])
reduceHead inv original = do
  result@(term,_) <- whnf 160 original
  guard (term /= original)
  pure result
  where
    fld k d = either (const Nothing) Just (field inv k d)
    definition s = M.lookup s (declarations inv)
    whnf fuel term | fuel <= (0 :: Int) = Nothing
                  | get "tag" term == String "definition" = do
        let s = string (get "symbol" term)
        d <- definition s
        if get "kind" d /= String "function" || not (terminationChecked inv d)
          || get "abstract" d /= Bool False || get "opaque" d /= Bool False then pure (term,[]) else do
          tree <- fld "compiled" d
          case runTree (fuel-1) tree (array (get "eliminations" term)) of
            Nothing -> pure (term,[])
            Just (value,steps) -> do
              (result,more) <- whnf (fuel-1) value
              pure (result,s:steps ++ more)
    whnf fuel term | get "tag" term == String "constructor" = do
      let es = array (get "eliminations" term); (args,rest) = span ((== String "apply") . get "tag") es
      case rest of
        p:ps | get "tag" p == String "project" -> do
          cd <- definition (string (get "symbol" term))
          owner <- fld "family" cd >>= definition . string
          guard (get "kind" owner == String "record")
          declaredConstructor <- fld "constructor" owner
          guard (declaredConstructor == get "symbol" term)
          fields <- map string . array <$> fld "fields" owner
          guard (length fields == length args)
          let matches = [i | (i,f) <- zip [0..] fields,f == string (get "symbol" p)]
          i <- case matches of [i] -> Just i; _ -> Nothing
          selected <- at i args >>= argument
          applied <- applySpine selected ps
          whnf (fuel-1) applied
        _ -> pure (term,[])
    whnf _ term = pure (term,[])
    runTree fuel tree es | fuel <= 0 = Nothing
      | get "tag" tree == String "done" = do
          let n = length (array (get "binders" tree))
          guard (length es >= n)
          args <- traverse argument (take n es)
          value <- substituteTerms (reverse args) (get "body" tree)
          applied <- applySpine value (drop n es)
          pure (applied,[])
      | get "tag" tree == String "case" = do
          i <- int (get "value" (get "argument" tree))
          selected <- at i es
          if get "copattern" tree == Bool True then do
            guard (get "tag" selected == String "project")
            branch <- unique (string (get "symbol" selected)) (array (get "constructors" tree))
            guard (get "arity" (get "branch" branch) == Number 0)
            runTree (fuel-1) (get "tree" (get "branch" branch)) (take i es ++ drop (i+1) es)
          else do
            guard (null (array (get "literals" tree)) && get "fallThrough" tree == Bool False)
            source <- argument selected
            let eta = get "eta" tree
            if eta /= Null then do
              -- Checked record eta exposes projections lazily, including a
              -- copattern-defined record whose proof component is unevaluated.
              values <- traverse (\f -> applySpine source [object ["tag" .= ("project" :: Text),"symbol" .= f]]) (array (get "fields" eta))
              runTree (fuel-1) (get "tree" (get "branch" eta)) (take i es ++ map application values ++ drop (i+1) es)
            else do
              (discriminant,steps) <- whnf (fuel-1) source
              if get "tag" discriminant == String "constructor" then do
                let branches = array (get "constructors" tree)
                case unique (string (get "symbol" discriminant)) branches of
                  Just branch -> do
                    let b = get "branch" branch; values = array (get "eliminations" discriminant)
                    guard (get "arity" b == toJSON (length values))
                    (result,more) <- runTree (fuel-1) (get "tree" b) (take i es ++ values ++ drop (i+1) es)
                    pure (result,steps ++ more)
                  Nothing -> runTree (fuel-1) (get "catchall" tree) es
              else identityCase fuel tree es i discriminant steps
      | otherwise = Nothing
    unique s bs = case filter ((== String s) . get "symbol") bs of [b] -> Just b; _ -> Nothing
    identityCase fuel tree es i discriminant steps = do
      let branches = array (get "constructors" tree)
      first <- case branches of b:_ -> Just b; _ -> Nothing
      cd <- definition (string (get "symbol" first))
      owner <- fld "family" cd >>= definition . string
      allConstructors <- array <$> fld "constructors" owner
      guard (get "kind" owner == String "datatype" && get "catchall" tree == Null)
      guard (length branches == length allConstructors && all (\c -> length (filter ((== c) . get "symbol") branches) == 1) allConstructors)
      histories <- traverse (\b -> do
        guard (get "arity" (get "branch" b) == Number 0)
        (result,history) <- runTree (fuel-1) (get "tree" (get "branch" b)) (take i es ++ drop (i+1) es)
        (normal,more) <- whnf (fuel-1) result
        guard (get "tag" normal == String "constructor" && get "symbol" normal == get "symbol" b && null (array (get "eliminations" normal)))
        pure (history ++ more)) branches
      pure (discriminant,steps ++ concat histories)

-- Stable closure keys omit source locations and ArgInfo, retaining all term
-- constructors, binding structure, identities and ordered eliminations.
canonicalTerm :: Value -> Value
canonicalTerm (Object fields) = Object (fmap canonicalTerm (foldr KM.delete fields
  ["info","$occurrence","$origin","sourceOrigin","reductionEvidence","checkedOrigin"]))
canonicalTerm (Array xs) = Array (fmap canonicalTerm xs)
canonicalTerm v = v

freeVariables :: Value -> [Int]
freeVariables = S.toAscList . collect 0
  where
    collect depth t@(Object fields)
      | get "tag" t == String "variable", Just i <- int (get "index" t) =
          (if i >= depth then S.singleton (i-depth) else S.empty) `S.union`
            S.unions (map (collect depth) (array (get "eliminations" t)))
      | get "binds" t `elem` [Bool True,Bool False], get "body" t /= Null =
          S.unions [collect (depth + if k == "body" && get "binds" t == Bool True then 1 else 0) x | (k,x) <- KM.toList fields]
      | otherwise = S.unions (map (collect depth) (KM.elems fields))
    collect depth (Array xs) = S.unions (map (collect depth) (foldr (:) [] xs))
    collect _ _ = S.empty

-- Replay checked case bindings under a simultaneous substitution. env is in
-- source telescope order, while its terms inhabit the target telescope of n
-- variables. Static and closure arguments need no target binder.
rewriteTree :: Inventory -> Int -> [Value] -> Value -> Maybe Value
rewriteTree inv n env tree = case string (get "tag" tree) of
  "absurd" -> do
    guard (length (array (get "binders" tree)) <= length env)
    pure $ set "binders" (toJSON (replicate n Null)) tree
  "done" -> do
    let count = length (array (get "binders" tree))
    guard (count <= length env)
    body <- substituteTerms (reverse (take count env)) (get "body" tree)
    applied <- applyTerms body (drop count env)
    pure $ set "body" applied $ set "binders" (toJSON (replicate n Null)) tree
  "case" | get "copattern" tree == Bool True -> do
    i <- int (get "value" (get "argument" tree))
    guard (i == length env)
    branches <- traverse (\b -> do
      child <- rewriteTree inv n env (get "tree" (get "branch" b))
      pure (set "branch" (set "tree" child (get "branch" b)) b)) (array (get "constructors" tree))
    pure $ set "argument" (set "value" (toJSON n) (get "argument" tree)) $ set "constructors" (toJSON branches) tree
  "case" -> do
    i <- int (get "value" (get "argument" tree))
    source <- at i env
    let selected = maybe source fst (reduceHead inv source)
    if get "tag" selected == String "constructor" then do
      guard (null (array (get "literals" tree)) && get "fallThrough" tree == Bool False)
      values <- traverse argument (array (get "eliminations" selected))
      let matching = filter ((== get "symbol" selected) . get "symbol") (array (get "constructors" tree))
          eta = get "eta" tree
      b <- case matching of
        [b] -> Just (get "branch" b)
        [] | get "constructor" eta == get "symbol" selected -> Just (get "branch" eta)
        _ -> Nothing
      guard (get "arity" b == toJSON (length values))
      rewriteTree inv n (take i env ++ values ++ drop (i+1) env) (get "tree" b)
    else do
      rewriteDynamic i selected
  _ -> Nothing
  where
   rewriteDynamic i selected = do
    guard (get "tag" selected == String "variable" && null (array (get "eliminations" selected)))
    index <- int (get "index" selected)
    let targetPosition = n-1-index
    guard (targetPosition >= 0)
    let branch c b = do
          arity <- int (get "arity" b)
          let n' = n-1+arity
              fields = [variable (n'-1-(targetPosition+k)) | k <- [0..arity-1]]
              reconstructed = object ["tag" .= ("constructor" :: Text),"symbol" .= c,"eliminations" .= map application fields]
              rebase k | k < index = variable k
                       | k == index = reconstructed
                       | otherwise = variable (k+arity-1)
          transported <- traverse (substituteTerms [rebase k | k <- [0..n-1]]) env
          body <- rewriteTree inv n' (take i transported ++ fields ++ drop (i+1) transported) (get "tree" b)
          pure (set "tree" body b)
    branches <- traverse (\b -> do
      child <- branch (get "symbol" b) (get "branch" b)
      pure (set "branch" child b)) (array (get "constructors" tree))
    eta <- if get "eta" tree == Null then pure Null else do
      let e = get "eta" tree
      child <- branch (get "constructor" e) (get "branch" e)
      pure (set "branch" child e)
    fallback <- if get "catchall" tree == Null then pure Null else rewriteTree inv n env (get "catchall" tree)
    guard (null (array (get "literals" tree)))
    pure $ set "argument" (set "value" (toJSON targetPosition) (get "argument" tree))
      $ set "constructors" (toJSON branches) $ set "eta" eta $ set "catchall" fallback tree
