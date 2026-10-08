{-# OPTIONS --safe #-}
module ComputedIndex where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Indexed using (Phase; idle; active; Flagged; flagged; flag)
open import SpecializedIndexed using (Evidence; off; on; read)

invert : Bool → Bool
invert true = false
invert false = true

phaseOf : Bool → Phase
phaseOf true = active
phaseOf false = idle

nextPhase : Bool → Phase
nextPhase b = phaseOf (invert b)

data Event : Phase → Set where
  event : (b : Bool) → Flagged (invert b) → Event (nextPhase b)

make : (b : Bool) → Event (phaseOf (invert b))
make b = event b (flagged (invert b))

observe : ∀ {p} → Event p → Bool
observe (event b witness) = flag witness

record Packet (A : Set) : Set where
  constructor packet
  field
    enabled : Bool
    evidence : Evidence A (invert enabled)
open Packet public

select : {A : Set} (p : Packet A) → Evidence A (invert (enabled p))
select p = evidence p

copy : {A : Set} → Packet A → Packet A
copy p = packet (enabled p) (select p)

makePacket : {A : Set} → Bool → A → Packet A
makePacket true x = packet true (off x)
makePacket false x = packet false (on x)

readPacket : {A : Set} → Packet A → A
readPacket p = read (select p)

record State : Set where
  constructor state
  field
    ordinary : Packet Bool
    current : Event (nextPhase false)
open State public

data Command : Set where
  set : Bool → Command
  keep : Command

step : Command → State → State
step (set x) before = state (makePacket x x) (make false)
step keep before = state (copy (ordinary before)) (current before)

readOrdinary : State → Bool
readOrdinary before = readPacket (ordinary before)

readCurrent : State → Bool
readCurrent before = observe (current before)

make-preserves : (b : Bool) → observe (make b) ≡ invert b
make-preserves b = refl

copy-preserves : {A : Set} (p : Packet A) → copy p ≡ p
copy-preserves p = refl

packet-preserves : {A : Set} (b : Bool) (x : A) → readPacket (makePacket b x) ≡ x
packet-preserves true x = refl
packet-preserves false x = refl

keep-preserves : (before : State) → step keep before ≡ before
keep-preserves before = refl

set-preserves : (x : Bool) (before : State) → readOrdinary (step (set x) before) ≡ x
set-preserves true before = refl
set-preserves false before = refl
