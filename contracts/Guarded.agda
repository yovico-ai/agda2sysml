{-# OPTIONS --safe #-}
open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality

module Guarded {ℓ : Level} (State : Set ℓ) (permitted : State → Bool)
  (update : State → State) where

data Command : Set where
  hold change : Command

data Outcome (before : State) : Set ℓ where
  applied : State → Outcome before
  unchanged refused : Outcome before

outcomeState : ∀ {before} → Outcome before → State
outcomeState (applied after) = after
outcomeState {before} unchanged = before
outcomeState {before} refused = before

step : (command : Command) → (before : State) → Outcome before
step hold before = unchanged
step change before with permitted before
... | true = applied (update before)
... | false = refused

-- Every refusal retains the complete initial state, regardless of the state
-- domain, chosen guard, or update operation.
refusal-preserves : (command : Command) (before : State)
  → step command before ≡ refused → outcomeState (step command before) ≡ before
refusal-preserves command before refused-result rewrite refused-result = refl

unchanged-preserves : (command : Command) (before : State)
  → step command before ≡ unchanged → outcomeState (step command before) ≡ before
unchanged-preserves command before unchanged-result rewrite unchanged-result = refl
