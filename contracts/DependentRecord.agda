{-# OPTIONS --safe #-}
module DependentRecord where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Indexed using (Phase; idle; active; Permit; waiting; granted; Flagged; flagged; retain; read; flag)

record Packet : Set where
  constructor packet
  field
    phase : Phase
    permit : Permit phase
    enabled : Bool
    marker : Flagged enabled
open Packet public

copy : Packet → Packet
copy p = packet (phase p) (retain (permit p)) (enabled p) (marker p)

rebuild : Packet → Packet
rebuild (packet phase permit enabled marker) = packet phase permit enabled marker

select : (p : Packet) → Permit (phase p)
select p = permit p

readPermit : Packet → Bool
readPermit p = read (select p)

readMarker : Packet → Bool
readMarker p = flag (marker p)

data Command : Set where
  prepare activate : Bool → Command
  keep : Command

step : Command → Packet → Packet
step (prepare value) before = packet idle (waiting value) false (flagged false)
step (activate value) before = packet active (granted value true) true (flagged true)
step keep before = copy (rebuild before)

copy-preserves : ∀ p → copy p ≡ p
copy-preserves p = refl

rebuild-preserves : ∀ p → rebuild p ≡ p
rebuild-preserves (packet phase permit enabled marker) = refl

select-preserves : ∀ p → select p ≡ permit p
select-preserves p = refl

marker-preserves : ∀ p → readMarker p ≡ enabled p
marker-preserves (packet ph witness b (flagged .b)) = refl

keep-preserves : ∀ before → step keep before ≡ before
keep-preserves (packet phase permit enabled marker) = refl

prepare-preserves : ∀ value before → readPermit (step (prepare value) before) ≡ value
prepare-preserves value before = refl

activate-preserves : ∀ value before → readPermit (step (activate value) before) ≡ value
activate-preserves value before = refl
