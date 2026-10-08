{-# OPTIONS --safe #-}
import Agda.Builtin.List
module Agda2SysML.Specialization (Atom Family Carrier : Set)
  (atomMeaning : Atom → Carrier)
  (familyMeaning : Family → Agda.Builtin.List.List Carrier → Carrier)
  (Value : Carrier → Set) where

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; sym; subst; Empty)

-- Parameter names are identities supplied by the checked telescope. Family
-- identities and argument order remain explicit even for phantom parameters.
data Type (Parameter : Set) : Set where
  parameter : Parameter → Type Parameter
  atom : Atom → Type Parameter
  family : Family → List (Type Parameter) → Type Parameter

mutual
  interpret : ∀ {P} → (P → Carrier) → Type P → Carrier
  interpret env (parameter p) = env p
  interpret env (atom a) = atomMeaning a
  interpret env (family f args) = familyMeaning f (interpretArgs env args)

  interpretArgs : ∀ {P} → (P → Carrier) → List (Type P) → List Carrier
  interpretArgs env [] = []
  interpretArgs env (t ∷ ts) = interpret env t ∷ interpretArgs env ts

mutual
  substitute : ∀ {P Q} → (P → Type Q) → Type P → Type Q
  substitute env (parameter p) = env p
  substitute env (atom a) = atom a
  substitute env (family f args) = family f (substituteArgs env args)

  substituteArgs : ∀ {P Q} → (P → Type Q) → List (Type P) → List (Type Q)
  substituteArgs env [] = []
  substituteArgs env (t ∷ ts) = substitute env t ∷ substituteArgs env ts

mutual
  substitution-preserves : ∀ {P Q} (replacement : P → Type Q) (env : Q → Carrier) (t : Type P)
    → interpret env (substitute replacement t) ≡ interpret (λ p → interpret env (replacement p)) t
  substitution-preserves replacement env (parameter p) = refl
  substitution-preserves replacement env (atom a) = refl
  substitution-preserves replacement env (family f args) =
    cong (familyMeaning f) (arguments-preserve replacement env args)

  arguments-preserve : ∀ {P Q} (replacement : P → Type Q) (env : Q → Carrier) (ts : List (Type P))
    → interpretArgs env (substituteArgs replacement ts) ≡ interpretArgs (λ p → interpret env (replacement p)) ts
  arguments-preserve replacement env [] = refl
  arguments-preserve replacement env (t ∷ ts)
    rewrite substitution-preserves replacement env t | arguments-preserve replacement env ts = refl

-- Closed instantiation has no remaining type variables. It does not identify
-- distinct family/argument keys merely because their value sets coincide.
closedEnvironment : Empty → Carrier
closedEnvironment ()

instantiate : ∀ {P} → (P → Type Empty) → Type P → Type Empty
instantiate = substitute

instantiate-preserves : ∀ {P} (replacement : P → Type Empty) (t : Type P)
  → interpret closedEnvironment (instantiate replacement t)
    ≡ interpret (λ p → interpret closedEnvironment (replacement p)) t
instantiate-preserves replacement = substitution-preserves replacement closedEnvironment

transport-roundtrip : ∀ {a b : Carrier} (equal : a ≡ b) (x : Value a)
  → subst Value (sym equal) (subst Value equal x) ≡ x
transport-roundtrip refl x = refl

reverse-transport-roundtrip : ∀ {a b : Carrier} (equal : a ≡ b) (x : Value b)
  → subst Value equal (subst Value (sym equal) x) ≡ x
reverse-transport-roundtrip refl x = refl

encode : ∀ {P} (replacement : P → Type Empty) (t : Type P)
  → Value (interpret (λ p → interpret closedEnvironment (replacement p)) t)
  → Value (interpret closedEnvironment (instantiate replacement t))
encode replacement t = subst Value (sym (instantiate-preserves replacement t))

decode : ∀ {P} (replacement : P → Type Empty) (t : Type P)
  → Value (interpret closedEnvironment (instantiate replacement t))
  → Value (interpret (λ p → interpret closedEnvironment (replacement p)) t)
decode replacement t = subst Value (instantiate-preserves replacement t)

-- Both directions preserve every value; specialization does not discard
-- fields or proof-relevant distinctions in the chosen carrier interpretation.
source-roundtrip : ∀ {P} (replacement : P → Type Empty) (t : Type P) x
  → decode replacement t (encode replacement t x) ≡ x
source-roundtrip replacement t x = reverse-transport-roundtrip (instantiate-preserves replacement t) x

target-roundtrip : ∀ {P} (replacement : P → Type Empty) (t : Type P) x
  → encode replacement t (decode replacement t x) ≡ x
target-roundtrip replacement t x = transport-roundtrip (instantiate-preserves replacement t) x

-- A first-order operation transports every input and its complete result.
-- Multi-input operations use a product carrier with its ordered field schema.
specializeOperation : ∀ {P} (replacement : P → Type Empty) (input output : Type P)
  → (Value (interpret (λ p → interpret closedEnvironment (replacement p)) input)
      → Value (interpret (λ p → interpret closedEnvironment (replacement p)) output))
  → Value (interpret closedEnvironment (instantiate replacement input))
  → Value (interpret closedEnvironment (instantiate replacement output))
specializeOperation replacement input output operation x =
  encode replacement output (operation (decode replacement input x))

operation-preserves : ∀ {P} (replacement : P → Type Empty) (input output : Type P) operation x
  → specializeOperation replacement input output operation (encode replacement input x)
    ≡ encode replacement output (operation x)
operation-preserves replacement input output operation x =
  cong (λ value → encode replacement output (operation value)) (source-roundtrip replacement input x)
