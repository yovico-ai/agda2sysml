{-# OPTIONS --safe --without-K #-}
module Agda2SysML.NaturalValues where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- ScalarValues::Natural includes infinity. The admitted target carrier is
-- its finite refinement, not the entire scalar extent. No machine bound is
-- imposed on either the source or the finite target values.
data ExtendedNatural : Set where
  finite : Nat → ExtendedNatural
  infinity : ExtendedNatural

data IsFinite : ExtendedNatural → Set where
  finite-value : ∀ n → IsFinite (finite n)

record NativeNatural : Set where
  constructor natural
  field
    value : ExtendedNatural
    finite-proof : IsFinite value

encode : Nat → NativeNatural
encode n = natural (finite n) (finite-value n)

decode : NativeNatural → Nat
decode (natural (finite n) (finite-value .n)) = n

source-roundtrip : ∀ n → decode (encode n) ≡ n
source-roundtrip n = refl

target-roundtrip : ∀ n → encode (decode n) ≡ n
target-roundtrip (natural (finite n) (finite-value .n)) = refl

infinity-refused : IsFinite infinity → ∀ {A : Set} → A
infinity-refused ()

-- These operations specify the finite restriction of native mathematical
-- arithmetic. In particular subtraction is truncated, never negative.
sourceAdd sourceMultiply sourceSubtract : Nat → Nat → Nat
sourceAdd m n = m + n
sourceMultiply m n = m * n
sourceSubtract m n = m - n

successor : NativeNatural → NativeNatural
successor n = encode (suc (decode n))

add multiply subtract : NativeNatural → NativeNatural → NativeNatural
add m n = encode (sourceAdd (decode m) (decode n))
multiply m n = encode (sourceMultiply (decode m) (decode n))
subtract m n = encode (sourceSubtract (decode m) (decode n))

equal less : NativeNatural → NativeNatural → Bool
equal m n = decode m == decode n
less m n = decode m < decode n

successor-preserves : ∀ n → successor (encode n) ≡ encode (suc n)
successor-preserves n = refl

addition-preserves : ∀ m n → add (encode m) (encode n) ≡ encode (m + n)
addition-preserves m n = refl

multiplication-preserves : ∀ m n → multiply (encode m) (encode n) ≡ encode (m * n)
multiplication-preserves m n = refl

subtraction-preserves : ∀ m n → subtract (encode m) (encode n) ≡ encode (m - n)
subtraction-preserves m n = refl

equality-preserves : ∀ m n → equal (encode m) (encode n) ≡ (m == n)
equality-preserves m n = refl

comparison-preserves : ∀ m n → less (encode m) (encode n) ≡ (m < n)
comparison-preserves m n = refl

-- Natural case splitting transports the predecessor in the successor
-- branch; it does not pass the original scrutinee as the recursive payload.
caseNat : ∀ {A : Set} → A → (Nat → A) → Nat → A
caseNat z s zero = z
caseNat z s (suc n) = s n

nativeCase : ∀ {A : Set} → A → (NativeNatural → A) → NativeNatural → A
nativeCase z s (natural (finite zero) (finite-value .zero)) = z
nativeCase z s (natural (finite (suc n)) (finite-value .(suc n))) = s (encode n)

case-preserves : ∀ {A : Set} (z : A) s n
  → nativeCase z (λ p → s (decode p)) (encode n) ≡ caseNat z s n
case-preserves z s zero = refl
case-preserves z s (suc n) = refl
