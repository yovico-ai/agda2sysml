{-# OPTIONS --safe #-}
module Agda2SysML.Foundation where

open import Agda.Builtin.Bool public
open import Agda.Builtin.Equality public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public

infixr 5 _++_
infixr 4 _∧_

data Empty : Set where

absurd : {A : Set} → Empty → A
absurd ()

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : (P → Empty) → Dec P

_∧_ : Bool → Bool → Bool
true ∧ b = b
false ∧ b = false

not : Bool → Bool
not true = false
not false = true

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl proof = proof

data IsJust {A : Set} : Maybe A → Set where
  present : {value : A} → IsJust (just value)

just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

orElse : {A : Set} → Maybe A → Maybe A → Maybe A
orElse nothing fallback = fallback
orElse (just value) fallback = just value
