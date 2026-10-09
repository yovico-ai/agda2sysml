{-# LANGUAGE OverloadedStrings #-}
-- | Conservative liveness of higher-order module parameters. Only forwarding
-- into another proven-unused parameter is ignored. Source terms stay intact.
module Agda2SysML.UnusedParameters (annotate) where

import Agda2SysML.Inventory
import qualified Agda2SysML.Reduction as Reduction
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Scientific (toBoundedInteger)

annotate :: Inventory -> Inventory
annotate inv = inv {declarations = M.mapWithKey attach (declarations inv)}
  where
    expanded = M.map (\d -> (d,source "type" d,source "compiled" d)) (declarations inv)
    source k d = either (const Null) id (field inv k d)
    candidates = M.mapMaybe candidate expanded
    candidate (d,ty,_) = do
      count <- integer (get "moduleParameters" d)
      let domains = telescope ty
          slots = S.fromList [i | (i,domain) <- zip [0..] (take count domains),higherOrder domain]
      if S.null slots || get "abstract" d == Bool True || get "opaque" d == Bool True
        || get "kind" d `notElem` map String ["function","datatype","record","constructor"]
        then Nothing else Just slots
    higherOrder ty = get "tag" (get "term" ty) == String "pi" && not (universeResult ty)
    universeResult ty = let t = get "term" ty in
      if get "tag" t == String "pi" then universeResult (get "body" (get "codomain" t))
      else get "tag" t == String "sort"
    fixed table = let next = M.mapWithKey (\s slots -> slots S.\\ live table s slots) table
      in if next == table then table else fixed next
    unused = fixed candidates
    attach s (Object fields) = Object (KM.insert "unusedModuleParameters"
      (toJSON (S.toAscList (M.findWithDefault S.empty s unused))) fields)
    attach _ d = d
    live table s slots = case M.lookup s expanded of
      Nothing -> slots
      Just (d,ty,tree) -> typeUses table [] 0 ty `S.union` case string (get "kind" d) of
        "function" | terminationChecked inv d ->
          let offset = projectionDrop (source "projection" d)
              env = map S.singleton [offset..length (telescope ty)-1]
          in maybe slots id (treeUses table env tree)
        "function" -> slots
        "datatype" -> owners table slots d (map string (array (source "constructors" d)))
        "record" -> owners table slots d [string (source "constructor" d)]
        "constructor" -> S.empty
        _ -> slots
    -- Family parameters are omitted from constructor terms, but remain in the
    -- constructor telescope. Every constructor must independently leave them dead.
    owners table slots d children = S.unions
      [slots S.\\ M.findWithDefault S.empty c table | c <- children]
      `S.union` if null children || get "parameters" d == Null then slots else S.empty
    typeUses table env position ty = let t = get "term" ty in
      if get "tag" t == String "pi" then
        let cod = get "codomain" t
            next = if get "binds" cod == Bool True then S.singleton position:env else env
        in uses table env (get "type" (get "domain" t)) `S.union`
          typeUses table next (position+1) (get "body" cod)
      else uses table env ty
    uses table env term = S.unions [at i env | i <- Reduction.freeVariables (mask table term)]
    -- Mask only complete definition applications. Partial, unknown and
    -- projection spines remain visible to the occurrence check.
    mask table term@(Object fields)
      | get "tag" term == String "definition"
      ,let s = string (get "symbol" term)
      ,Just (_,ty,_) <- M.lookup s expanded
      ,let es = array (get "eliminations" term)
      ,length es == length (telescope ty)
      ,all ((== String "apply") . get "tag") es =
          let dead = M.findWithDefault S.empty s table
              args = [if S.member i dead then Null else mask table e | (i,e) <- zip [0..] es]
          in Object (KM.insert "eliminations" (toJSON args) (fmap (mask table) fields))
      | otherwise = Object (fmap (mask table) fields)
    mask table (Array xs) = Array (fmap (mask table) xs)
    mask _ value = value
    treeUses table env tree = case string (get "tag" tree) of
      "done" -> do
        let count = length (array (get "binders" tree))
            missing = length env - count
        if missing < 0 then Nothing else do
          applied <- Reduction.applyTerms (Reduction.shift missing (get "body" tree))
            [Reduction.variable (length env-1-i) | i <- [count..length env-1]]
          Just (uses table (reverse env) applied)
      "absurd" -> if length (array (get "binders" tree)) == length env then Just S.empty else Nothing
      "case" -> do
        i <- integer (get "value" (get "argument" tree))
        let copattern = get "copattern" tree == Bool True
        if i < 0 || (if copattern then i /= length env else i >= length env)
          || not (null (array (get "literals" tree))) then Nothing else do
          let branch b = do
                n <- integer (get "arity" b)
                if n < 0 then Nothing else treeUses table
                  (take i env ++ replicate n S.empty ++ drop (i+1) env) (get "tree" b)
          ordinary <- traverse (branch . get "branch") (array (get "constructors" tree))
          eta <- if get "eta" tree == Null then Just S.empty else branch (get "branch" (get "eta" tree))
          fallback <- if get "catchall" tree == Null then Just S.empty else treeUses table env (get "catchall" tree)
          pure (S.unions (eta:fallback:ordinary) `S.union` if copattern then S.empty else at i env)
      _ -> Nothing

telescope :: Value -> [Value]
telescope ty = let t = get "term" ty in if get "tag" t == String "pi"
  then get "type" (get "domain" t):telescope (get "body" (get "codomain" t)) else []
integer :: Value -> Maybe Int
integer (Number n) = toBoundedInteger n
integer _ = Nothing
at :: Int -> [S.Set Int] -> S.Set Int
at i xs | i >= 0 = case drop i xs of x:_ -> x; _ -> S.empty
        | otherwise = S.empty
projectionDrop :: Value -> Int
projectionDrop p = maybe 0 (max 0 . subtract 1) (integer (get "index" p))
