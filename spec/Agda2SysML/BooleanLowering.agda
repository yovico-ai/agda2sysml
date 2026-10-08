{-# OPTIONS --safe #-}
module Agda2SysML.BooleanLowering where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda2SysML.Foundation using (Bool; true; false; _≡_; refl; cong; trans)

data Fin : Nat → Set where
  first : {n : Nat} → Fin (suc n)
  next : {n : Nat} → Fin n → Fin (suc n)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)
infixr 5 _∷_

lookup : {A : Set} {n : Nat} → Fin n → Vec A n → A
lookup first (x ∷ xs) = x
lookup (next i) (x ∷ xs) = lookup i xs

remove : {A : Set} {n : Nat} → Fin (suc n) → Vec A (suc n) → Vec A n
remove first (x ∷ xs) = xs
remove {n = zero} (next ()) (x ∷ xs)
remove {n = suc n} (next i) (x ∷ xs) = x ∷ remove i xs

map : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-lookup : {A B : Set} {n : Nat} (f : A → B) (i : Fin n) (xs : Vec A n)
  → lookup i (map f xs) ≡ f (lookup i xs)
map-lookup f first (x ∷ xs) = refl
map-lookup f (next i) (x ∷ xs) = map-lookup f i xs

map-remove : {A B : Set} {n : Nat} (f : A → B)
  (i : Fin (suc n)) (xs : Vec A (suc n))
  → remove i (map f xs) ≡ map f (remove i xs)
map-remove f first (x ∷ xs) = refl
map-remove {n = zero} f (next ()) (x ∷ xs)
map-remove {n = suc n} f (next i) (x ∷ xs) = cong (λ rest → f x ∷ rest) (map-remove f i xs)

choose : {A : Set} → Bool → A → A → A
choose true yes no = yes
choose false yes no = no

-- Compiled constructor matching removes the matched nullary argument.
data Cases : Nat → Set where
  value : {n : Nat} → Bool → Cases n
  read-var : {n : Nat} → Fin n → Cases n
  split : {n : Nat} → Fin (suc n) → Cases n → Cases n → Cases (suc n)

source : {n : Nat} → Cases n → Vec Bool n → Bool
source (value b) env = b
source (read-var i) env = lookup i env
source (split i yes no) env = choose (lookup i env)
  (source yes (remove i env)) (source no (remove i env))

-- Native Boolean expressions retain the original calculation inputs.
data Expr (n : Nat) : Set where
  literal : Bool → Expr n
  input : Fin n → Expr n
  conditional : Expr n → Expr n → Expr n → Expr n

target : {n : Nat} → Expr n → Vec Bool n → Bool
target (literal b) env = b
target (input i) env = lookup i env
target (conditional test yes no) env = choose (target test env)
  (target yes env) (target no env)

lower : {n m : Nat} → Cases n → Vec (Expr m) n → Expr m
lower (value b) bindings = literal b
lower (read-var i) bindings = lookup i bindings
lower (split i yes no) bindings = conditional (lookup i bindings)
  (lower yes (remove i bindings)) (lower no (remove i bindings))

cong₃ : {A B C D : Set} (f : A → B → C → D)
  {a a′ : A} {b b′ : B} {c c′ : C}
  → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

-- The law includes arbitrary substitutions, not just identity environments.
lower-preserves : {n m : Nat} (tree : Cases n)
  (bindings : Vec (Expr m) n) (env : Vec Bool m)
  → source tree (map (λ term → target term env) bindings)
    ≡ target (lower tree bindings) env
lower-preserves (value b) bindings env = refl
lower-preserves (read-var i) bindings env = map-lookup (λ term → target term env) i bindings
lower-preserves (split i yes no) bindings env = cong₃ choose
  (map-lookup (λ term → target term env) i bindings)
  (trans (cong (source yes) (map-remove (λ term → target term env) i bindings))
    (lower-preserves yes (remove i bindings) env))
  (trans (cong (source no) (map-remove (λ term → target term env) i bindings))
    (lower-preserves no (remove i bindings) env))
