{-# OPTIONS --safe #-}
module Agda2SysML.Sharing where

open import Agda2SysML.Foundation
open import Agda.Builtin.Nat

-- A store may share arbitrary values. The lookup relation carries the value
-- found, so an identifier can never be reused for an unequal value.
data At {A : Set} : List A → Nat → A → Set where
  here : {x : A} {xs : List A} → At (x ∷ xs) zero x
  there : {x y : A} {xs : List A} {n : Nat}
    → At xs n x → At (y ∷ xs) (suc n) x

at-functional : {A : Set} {xs : List A} {n : Nat} {x y : A}
  → At xs n x → At xs n y → x ≡ y
at-functional here here = refl
at-functional (there p) (there q) = at-functional p q

-- Labels encode compiler-node kind and scalar metadata. Children remain in
-- source order, including every argument and dependent binder component.
data Tree (Label : Set) : Set where
  atom : Label → Tree Label
  fork : Label → Tree Label → Tree Label → Tree Label

data Shared {Label : Set} (store : List (Tree Label)) : Tree Label → Set where
  inline-atom : (l : Label) → Shared store (atom l)
  inline-fork : (l : Label) {a b : Tree Label}
    → Shared store a → Shared store b → Shared store (fork l a b)
  reference : {n : Nat} {t : Tree Label} → At store n t → Shared store t

expand : {L : Set} {store : List (Tree L)} {t : Tree L}
  → Shared store t → Tree L
expand (inline-atom l) = atom l
expand (inline-fork l a b) = fork l (expand a) (expand b)
expand (reference {t = t} _) = t

reconstruction : {L : Set} {store : List (Tree L)} {t : Tree L}
  → (shared : Shared store t) → expand shared ≡ t
reconstruction (inline-atom l) = refl
reconstruction (inline-fork l a b) =
  trans (cong (λ x → fork l x (expand b)) (reconstruction a))
    (cong (fork l _) (reconstruction b))
reconstruction (reference p) = refl
