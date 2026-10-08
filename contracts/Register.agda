{-# OPTIONS --safe #-}
module Register where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- A register with independently writable Boolean value and enable flag.
record State : Set where
  constructor state
  field
    value enabled : Bool
open State public

data Command : Set where
  write : Bool → Command
  enable : Bool → Command
  replace : State → Command
  retain : Command

step : Command → State → State
step (write x) before = state x (enabled before)
step (enable x) before = state (value before) x
step (replace after) before = after
step retain before = before

-- Each update preserves the independent field for every input state/value.
write-preserves-enabled : ∀ x before → enabled (step (write x) before) ≡ enabled before
write-preserves-enabled x before = refl

enable-preserves-value : ∀ x before → value (step (enable x) before) ≡ value before
enable-preserves-value x before = refl

retain-preserves : ∀ before → step retain before ≡ before
retain-preserves before = refl

replace-complete : ∀ after before → step (replace after) before ≡ after
replace-complete after before = refl

-- These general product laws also exercise compiler record-pattern handling.
rebuild : State → State
rebuild (state x y) = state x y

rebuild-preserves : ∀ before → rebuild before ≡ before
rebuild-preserves (state x y) = refl
