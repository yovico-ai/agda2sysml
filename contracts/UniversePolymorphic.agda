{-# OPTIONS --safe #-}
module UniversePolymorphic where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Box {a : Level} (A : Set a) : Set a where
  constructor box
  field contents : A
open Box public

record Lift {a : Level} (b : Level) (A : Set a) : Set (a ⊔ b) where
  constructor lift
  field lower : A
open Lift public

identity : ∀ {a} {A : Set a} → A → A
identity x = x

retain : ∀ {a} {A : Set a} → Box A → Box A
retain x = x

enclose : ∀ {a} (b c : Level) {A : Set a} → A → Box (Lift (b ⊔ c) A)
enclose b c x = box (lift x)

identity-preserves : ∀ {a} {A : Set a} (x : A) → identity x ≡ x
identity-preserves x = refl

retain-preserves : ∀ {a} {A : Set a} (x : Box A) → retain x ≡ x
retain-preserves x = refl

enclose-preserves : ∀ {a} (b c : Level) {A : Set a} (x : A) → lower (contents (enclose b c x)) ≡ x
enclose-preserves b c x = refl

box-roundtrip : ∀ {a} {A : Set a} (x : Box A) → box (contents x) ≡ x
box-roundtrip x = refl

lift-roundtrip : ∀ {a} {b} {A : Set a} (x : Lift b A) → lift (lower x) ≡ x
lift-roundtrip x = refl

record State : Set (lsuc (lsuc lzero)) where
  constructor state
  field
    ordinary : Box Bool
    raised : Box (Lift (lsuc (lsuc lzero)) Bool)
open State public

data Command : Set where
  set : Bool → Command
  keep : Command

step : Command → State → State
step (set x) before = state (retain (box x)) (enclose (lsuc lzero) (lsuc (lsuc lzero)) x)
step keep before = state (identity (ordinary before)) (identity (raised before))

readOrdinary : State → Bool
readOrdinary before = contents (ordinary before)

readRaised : State → Bool
readRaised before = lower (contents (raised before))

keep-preserves : ∀ before → step keep before ≡ before
keep-preserves before = refl

set-ordinary : ∀ x before → readOrdinary (step (set x) before) ≡ x
set-ordinary x before = refl

set-raised : ∀ x before → readRaised (step (set x) before) ≡ x
set-raised x before = refl
