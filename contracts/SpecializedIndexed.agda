{-# OPTIONS --safe #-}
module SpecializedIndexed where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Indexed using (Phase; idle; active)
open import UniversePolymorphic using (Lift; lift; lower; Box; box; contents)

data Evidence {a : Level} (A : Set a) : Bool → Set a where
  off : A → Evidence A false
  on : A → Evidence A true

data Permit {a : Level} (A : Set a) : Phase → Set a where
  waiting : A → Permit A idle
  granted : A → Permit A active

retain : ∀ {a} {A : Set a} {b} → Evidence A b → Evidence A b
retain e = e

read : ∀ {a} {A : Set a} {b} → Evidence A b → A
read (off x) = x
read (on x) = x

readPermit : ∀ {a} {A : Set a} {phase} → Permit A phase → A
readPermit (waiting x) = x
readPermit (granted x) = x

record Packet {a : Level} (A : Set a) : Set a where
  constructor packet
  field
    enabled : Bool
    evidence : Evidence A enabled
    phase : Phase
    permit : Permit A phase
open Packet public

copy : ∀ {a} {A : Set a} → Packet A → Packet A
copy p = packet (enabled p) (retain (evidence p)) (phase p) (permit p)

rebuild : ∀ {a} {A : Set a} → Packet A → Packet A
rebuild (packet b e phase permit) = packet b e phase permit

select : ∀ {a} {A : Set a} (p : Packet A) → Evidence A (enabled p)
select p = evidence p

make : ∀ {a} {A : Set a} → A → Packet A
make x = packet true (on x) active (granted x)

readPacket : ∀ {a} {A : Set a} → Packet A → A
readPacket p = read (select p)

copy-preserves : ∀ {a} {A : Set a} (p : Packet A) → copy p ≡ p
copy-preserves p = refl

rebuild-preserves : ∀ {a} {A : Set a} (p : Packet A) → rebuild p ≡ p
rebuild-preserves (packet b e phase permit) = refl

select-preserves : ∀ {a} {A : Set a} (p : Packet A) → select p ≡ evidence p
select-preserves p = refl

make-preserves : ∀ {a} {A : Set a} (x : A) → readPacket (make x) ≡ x
make-preserves x = refl

record State : Set (lsuc lzero) where
  constructor state
  field
    ordinary : Packet Bool
    raised : Packet (Lift (lsuc lzero) Bool)
    wrapped : Box (Evidence Bool false)
    wrappedTrue : Box (Evidence Bool true)
open State public

data Command : Set where
  set : Bool → Command
  keep : Command

step : Command → State → State
step (set x) before = state (make x) (make (lift x)) (box (off x)) (box (on x))
step keep before = state (copy (rebuild (ordinary before))) (copy (raised before)) (wrapped before) (wrappedTrue before)

readOrdinary : State → Bool
readOrdinary before = readPacket (ordinary before)

readRaised : State → Bool
readRaised before = lower (readPermit (permit (raised before)))

readWrapped : State → Bool
readWrapped before = read (contents (wrapped before))

readWrappedTrue : State → Bool
readWrappedTrue before = read (contents (wrappedTrue before))

keep-preserves : ∀ before → step keep before ≡ before
keep-preserves (state (packet b e phase permit) raised wrapped wrappedTrue) = refl

set-ordinary : ∀ x before → readOrdinary (step (set x) before) ≡ x
set-ordinary x before = refl

set-raised : ∀ x before → readRaised (step (set x) before) ≡ x
set-raised x before = refl

set-wrapped : ∀ x before → readWrapped (step (set x) before) ≡ x
set-wrapped x before = refl

set-wrapped-true : ∀ x before → readWrappedTrue (step (set x) before) ≡ x
set-wrapped-true x before = refl
