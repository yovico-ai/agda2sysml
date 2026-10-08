{-# OPTIONS --safe #-}
module Agda2SysML.NaturalIndices where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality
open import Agda2SysML.BooleanLowering using (Fin; first; next; Vec; []; _∷_)
open import Agda2SysML.Foundation using (cong)

data _<_ : Nat → Nat → Set where
  zero-below : ∀ {n} → zero < suc n
  successor-below : ∀ {m n} → m < n → suc m < suc n

ordinal : ∀ {n} → Fin n → Nat
ordinal first = zero
ordinal (next i) = suc (ordinal i)

ordinal-bounded : ∀ {n} (i : Fin n) → ordinal i < n
ordinal-bounded first = zero-below
ordinal-bounded (next i) = successor-below (ordinal-bounded i)

length : ∀ {A : Set} {n} → Vec A n → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

length-index : ∀ {A : Set} {n} (xs : Vec A n) → length xs ≡ n
length-index [] = refl
length-index (x ∷ xs) = cong suc (length-index xs)
