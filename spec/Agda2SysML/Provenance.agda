{-# OPTIONS --safe #-}
module Agda2SysML.Provenance where

open import Agda2SysML.Foundation

module Origins (Source : Set) where
  record Located (A : Set) : Set where
    constructor located
    field
      origin : Source
      value : A
  open Located public

  transform : {A B : Set} → (A → B) → Located A → Located B
  transform f (located source value) = located source (f value)

  transform-preserves-origin : {A B : Set} (f : A → B) (input : Located A)
    → origin (transform f input) ≡ origin input
  transform-preserves-origin f (located source value) = refl

  transform-composes : {A B C : Set} (f : A → B) (g : B → C) (input : Located A)
    → transform g (transform f input) ≡ transform (λ value → g (f value)) input
  transform-composes f g (located source value) = refl
