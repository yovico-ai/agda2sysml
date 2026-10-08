{-# OPTIONS --safe #-}
module RegisterWorkflow where

open import Agda.Builtin.Equality
open import Register public using (State; Command; step; retain; replace)

-- Sequential composition retains the full intermediate state. Both commands
-- and every input state remain arbitrary throughout these laws.
sequence : Command → Command → State → State
sequence first second before = step second (step first before)

retain-left : ∀ command before → sequence retain command before ≡ step command before
retain-left command before = refl

retain-right : ∀ command before → sequence command retain before ≡ step command before
retain-right command before = refl

sequence-associative : ∀ first second third before
  → step third (sequence first second before) ≡ sequence second third (step first before)
sequence-associative first second third before = refl

replace-final : ∀ command after before → sequence command (replace after) before ≡ after
replace-final command after before = refl
