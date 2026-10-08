{-# OPTIONS --safe #-}
module Parameterized where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Box (A : Set) : Set where
  constructor box
  field contents : A
open Box public

data Choice (A B : Set) : Set where
  first : A → Choice A B
  second : B → Choice A B

retain : {A : Set} → Box A → Box A
retain value = value

replace : {A : Set} → A → Box A → Box A
replace value before = box value

choose : {A : Set} → Choice A A → A
choose (first value) = value
choose (second value) = value

retain-preserves : ∀ {A} (value : Box A) → retain value ≡ value
retain-preserves value = refl

replace-contents : ∀ {A} (value : A) before → contents (replace value before) ≡ value
replace-contents value before = refl

box-roundtrip : ∀ {A} (value : Box A) → box (contents value) ≡ value
box-roundtrip value = refl

choose-first : ∀ {A} (value : A) → choose (first value) ≡ value
choose-first value = refl

choose-second : ∀ {A} (value : A) → choose (second value) ≡ value
choose-second value = refl

data Colour : Set where
  red blue : Colour

-- Independent typed registers retain their own concrete value domains.
record State : Set where
  constructor state
  field
    flag : Box Bool
    colour : Box Colour
open State public

data Command : Set where
  setFlag : Choice Bool Bool → Command
  setColour : Choice Colour Colour → Command
  keep : Command

step : Command → State → State
step (setFlag value) before = state (replace (choose value) (flag before)) (retain (colour before))
step (setColour value) before = state (retain (flag before)) (replace (choose value) (colour before))
step keep before = before

flag-preserves-colour : ∀ value before → colour (step (setFlag value) before) ≡ colour before
flag-preserves-colour value before = refl

colour-preserves-flag : ∀ value before → flag (step (setColour value) before) ≡ flag before
colour-preserves-flag value before = refl

keep-preserves : ∀ before → step keep before ≡ before
keep-preserves before = refl
