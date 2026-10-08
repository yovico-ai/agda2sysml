{-# OPTIONS --safe #-}
module Indexed where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data Phase : Set where
  idle active : Phase

data Permit : Phase → Set where
  waiting : Bool → Permit idle
  granted : Bool → Bool → Permit active

data Flagged : Bool → Set where
  flagged : (flag : Bool) → Flagged flag

retain : ∀ {phase} → Permit phase → Permit phase
retain value = value

read : ∀ {phase} → Permit phase → Bool
read (waiting value) = value
read (granted value approved) = value

approve : Permit idle → Permit active
approve (waiting value) = granted value true

flag : ∀ {b} → Flagged b → Bool
flag (flagged b) = b

record State : Set where
  constructor state
  field
    pending : Permit idle
    ready : Permit active
    marked : Flagged true
open State public

data Command : Set where
  set : Bool → Command
  keep : Command

step : Command → State → State
step (set value) before = state (waiting value) (approve (waiting value)) (flagged true)
step keep before = state (retain (pending before)) (retain (ready before)) (marked before)

readPending : State → Bool
readPending before = read (pending before)

readReady : State → Bool
readReady before = read (ready before)

readMarked : State → Bool
readMarked before = flag (marked before)

retain-preserves : ∀ {phase} (value : Permit phase) → retain value ≡ value
retain-preserves value = refl

approve-preserves : (value : Permit idle) → read (approve value) ≡ read value
approve-preserves (waiting value) = refl

flag-preserves : ∀ {b} (value : Flagged b) → flag value ≡ b
flag-preserves (flagged b) = refl

keep-preserves : ∀ before → step keep before ≡ before
keep-preserves before = refl

set-pending : ∀ value before → readPending (step (set value) before) ≡ value
set-pending value before = refl

set-ready : ∀ value before → readReady (step (set value) before) ≡ value
set-ready value before = refl
