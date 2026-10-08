{-# OPTIONS --safe #-}
module DependentPayload where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Indexed using (Phase; idle; active; Permit; waiting; granted; Flagged; flagged; read; flag)
open import DependentRecord using (Packet; phase)
open import SpecializedIndexed using (Evidence; off; on)
import SpecializedIndexed as Generic
open import UniversePolymorphic using (Lift; lift; lower)

data Event : Set where
  quiet : Bool → Event
  marked : (b : Bool) → Flagged b → Event
  authorized : (phase : Phase) → Permit phase → (b : Bool) → Flagged b → Event
  embedded : (packetValue : Packet) → Permit (phase packetValue) → Event

copy : Event → Event
copy (quiet x) = quiet x
copy (marked b marker) = marked b marker
copy (authorized phase permit b marker) = authorized phase permit b marker
copy (embedded packetValue permit) = embedded packetValue permit

observe : Event → Bool
observe (quiet x) = x
observe (marked b marker) = flag marker
observe (authorized phase permit b marker) = read permit
observe (embedded packetValue permit) = read permit

-- Matching a dependent payload refines the earlier index, including dotted
-- source patterns. Every possible payload constructor remains accounted for.
matched : Event → Bool
matched (quiet x) = x
matched (marked .b (flagged b)) = b
matched (authorized .idle (waiting x) b marker) = x
matched (authorized .active (granted x approved) b marker) = x
matched (embedded packetValue permit) = read permit

copy-preserves : (event : Event) → copy event ≡ event
copy-preserves (quiet x) = refl
copy-preserves (marked b marker) = refl
copy-preserves (authorized phase permit b marker) = refl
copy-preserves (embedded packetValue permit) = refl

matching-preserves : (event : Event) → matched event ≡ observe event
matching-preserves (quiet x) = refl
matching-preserves (marked .b (flagged b)) = refl
matching-preserves (authorized .idle (waiting x) b marker) = refl
matching-preserves (authorized .active (granted x approved) b marker) = refl
matching-preserves (embedded packetValue permit) = refl

data Envelope {a : Level} (A : Set a) : Bool → Set a where
  message : (b : Bool) → Evidence A b → Envelope A b
  plain : A → Envelope A false

copyEnvelope : ∀ {a} {A : Set a} {b} → Envelope A b → Envelope A b
copyEnvelope (message b evidence) = message b evidence
copyEnvelope (plain x) = plain x

readEnvelope : ∀ {a} {A : Set a} {b} → Envelope A b → A
readEnvelope (message b evidence) = Generic.read evidence
readEnvelope (plain x) = x

envelope-copy : ∀ {a} {A : Set a} {b} (value : Envelope A b) → copyEnvelope value ≡ value
envelope-copy (message b evidence) = refl
envelope-copy (plain x) = refl

record State : Set (lsuc lzero) where
  constructor state
  field
    event : Event
    ordinary : Envelope Bool false
    raised : Envelope (Lift (lsuc lzero) Bool) true
open State public

data Command : Set where
  set : Bool → Command
  keep : Command

step : Command → State → State
step (set x) before = state (authorized active (granted x true) true (flagged true))
  (message false (off x)) (message true (on (lift x)))
step keep before = state (copy (event before)) (copyEnvelope (ordinary before)) (copyEnvelope (raised before))

readEvent : State → Bool
readEvent before = observe (event before)

readMatched : State → Bool
readMatched before = matched (event before)

readOrdinary : State → Bool
readOrdinary before = readEnvelope (ordinary before)

readRaised : State → Bool
readRaised before = lower (readEnvelope (raised before))

keep-preserves : ∀ before → step keep before ≡ before
keep-preserves (state event ordinary raised)
  rewrite copy-preserves event | envelope-copy ordinary | envelope-copy raised = refl

set-event : ∀ x before → readEvent (step (set x) before) ≡ x
set-event x before = refl

set-ordinary : ∀ x before → readOrdinary (step (set x) before) ≡ x
set-ordinary x before = refl

set-raised : ∀ x before → readRaised (step (set x) before) ≡ x
set-raised x before = refl
