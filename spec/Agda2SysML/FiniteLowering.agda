{-# OPTIONS --safe #-}
module Agda2SysML.FiniteLowering where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda2SysML.Foundation using (Bool; true; false; _≡_; refl; cong; trans)
open import Agda2SysML.BooleanLowering using (Fin; first; next; Vec; []; _∷_; lookup; remove; map; map-lookup; map-remove; choose)

-- Each constructor of a closed, payload-free domain has a distinct finite
-- index. Branches are exhaustive functions on that finite domain.
data Cases (k : Nat) : Nat → Set where
  value : ∀ {n} → Fin k → Cases k n
  read-var : ∀ {n} → Fin n → Cases k n
  split : ∀ {n} → Fin (suc n) → (Fin k → Cases k n) → Cases k (suc n)

source : ∀ {k n} → Cases k n → Vec (Fin k) n → Fin k
source (value x) env = x
source (read-var i) env = lookup i env
source (split i branches) env = source (branches (lookup i env)) (remove i env)

data Expr (k n : Nat) : Set where
  literal : Fin k → Expr k n
  input : Fin n → Expr k n
  select : Expr k n → (Fin k → Expr k n) → Expr k n

target : ∀ {k n} → Expr k n → Vec (Fin k) n → Fin k
target (literal x) env = x
target (input i) env = lookup i env
target (select discriminant branches) env = target (branches (target discriminant env)) env

lower : ∀ {k n m} → Cases k n → Vec (Expr k m) n → Expr k m
lower (value x) bindings = literal x
lower (read-var i) bindings = lookup i bindings
lower (split i branches) bindings = select (lookup i bindings)
  (λ choice → lower (branches choice) (remove i bindings))

lower-preserves : ∀ {k n m} (tree : Cases k n)
  (bindings : Vec (Expr k m) n) (env : Vec (Fin k) m)
  → source tree (map (λ term → target term env) bindings)
    ≡ target (lower tree bindings) env
lower-preserves (value x) bindings env = refl
lower-preserves (read-var i) bindings env = map-lookup (λ term → target term env) i bindings
lower-preserves (split i branches) bindings env = trans
  (cong (λ choice → source (branches choice) (remove i (map (λ term → target term env) bindings)))
    (map-lookup (λ term → target term env) i bindings))
  (trans (cong (source (branches (target (lookup i bindings) env)))
    (map-remove (λ term → target term env) i bindings))
    (lower-preserves (branches (target (lookup i bindings) env)) (remove i bindings) env))

-- Semantics of nested constructor-equality tests. Once a constructor failed,
-- the remaining alternatives are reindexed; the last alternative is exhaustive.
is-first : ∀ {n} → Fin (suc n) → Bool
is-first first = true
is-first (next _) = false

remaining : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
remaining first = first
remaining (next i) = i

native-select : ∀ {n} {A : Set} → Fin (suc n) → Vec A (suc n) → A
native-select {zero} i (x ∷ []) = x
native-select {suc n} i (x ∷ xs) = choose (is-first i) x (native-select (remaining i) xs)

native-select-preserves : ∀ {n} {A : Set} (i : Fin (suc n)) (values : Vec A (suc n))
  → native-select i values ≡ lookup i values
native-select-preserves {zero} first (x ∷ []) = refl
native-select-preserves {zero} (next ()) (x ∷ [])
native-select-preserves {suc n} first (x ∷ xs) = refl
native-select-preserves {suc n} (next i) (x ∷ xs) = native-select-preserves i xs
