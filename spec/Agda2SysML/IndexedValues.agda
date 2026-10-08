{-# OPTIONS --safe --without-K #-}
module Agda2SysML.IndexedValues where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

-- Constructor-specific payloads determine the index of each domain value.
-- The compiler gate restricts index expressions to finite values/projections.
module Family {ℓ ℓt ℓp : Level} (Index : Set ℓ) (Tag : Set ℓt)
  (Payload : Tag → Set ℓp) (resultIndex : (tag : Tag) → Payload tag → Index) where

  data Source : Index → Set (ℓ ⊔ ℓt ⊔ ℓp) where
    construct : (tag : Tag) (payload : Payload tag) → Source (resultIndex tag payload)

  Carrier : Set (ℓt ⊔ ℓp)
  Carrier = Σ Tag Payload

  indexOf : Carrier → Index
  indexOf (tag , payload) = resultIndex tag payload

  Fibre : Index → Set (ℓ ⊔ ℓt ⊔ ℓp)
  Fibre i = Σ Carrier (λ value → indexOf value ≡ i)

  encode : ∀ {i} → Source i → Fibre i
  encode (construct tag payload) = (tag , payload) , refl

  decode : ∀ {i} → Fibre i → Source i
  decode ((tag , payload) , refl) = construct tag payload

  decode-encode : ∀ {i} (value : Source i) → decode (encode value) ≡ value
  decode-encode (construct tag payload) = refl

  encode-decode : ∀ {i} (value : Fibre i) → encode (decode value) ≡ value
  encode-decode ((tag , payload) , refl) = refl

  constructor-index : (tag : Tag) (payload : Payload tag)
    → indexOf (fst (encode (construct tag payload))) ≡ resultIndex tag payload
  constructor-index tag payload = refl

  -- The native result assertion supplies exactly the equality needed to
  -- regard an unrefined carrier as a member of the expected result fibre.
  ResultContract : Index → Carrier → Set ℓ
  ResultContract expected value = indexOf value ≡ expected

  admit-result : (expected : Index) (value : Carrier)
    → ResultContract expected value → Fibre expected
  admit-result expected value proof = value , proof

  result-contract-preserves : (expected : Index) (value : Carrier)
    (proof : ResultContract expected value) → fst (admit-result expected value proof) ≡ value
  result-contract-preserves expected value proof = refl

  constructor-result-contract : (tag : Tag) (payload : Payload tag) (expected : Index)
    → resultIndex tag payload ≡ expected
    → ResultContract expected (fst (encode (construct tag payload)))
  constructor-result-contract tag payload expected proof = proof

  constructor-result-reflects : (tag : Tag) (payload : Payload tag) (expected : Index)
    → ResultContract expected (fst (encode (construct tag payload)))
    → resultIndex tag payload ≡ expected
  constructor-result-reflects tag payload expected proof = proof

  constructor-result-refuses-mismatch : (tag : Tag) (payload : Payload tag) (expected : Index)
    → (resultIndex tag payload ≡ expected → Empty)
    → ResultContract expected (fst (encode (construct tag payload))) → Empty
  constructor-result-refuses-mismatch tag payload expected mismatch proof =
    mismatch (constructor-result-reflects tag payload expected proof)

  native : (next : Index → Index) → (∀ {i} → Source i → Source (next i))
    → ∀ {i} → Fibre i → Fibre (next i)
  native next operation value = encode (operation (decode value))

  operation-preserves : (next : Index → Index) (operation : ∀ {i} → Source i → Source (next i))
    → ∀ {i} (value : Source i) → native next operation (encode value) ≡ encode (operation value)
  operation-preserves next operation (construct tag payload) = refl

  -- Branch observation covers constructor dispatch and ordered payload access.
  observe : ∀ {ℓr} {Result : Set ℓr} → ((tag : Tag) → Payload tag → Result)
    → ∀ {i} → Source i → Result
  observe branch (construct tag payload) = branch tag payload

  dispatch-preserves : ∀ {ℓr} {Result : Set ℓr} (branch : (tag : Tag) → Payload tag → Result)
    → ∀ {i} (value : Source i)
    → branch (fst (fst (encode value))) (snd (fst (encode value))) ≡ observe branch value
  dispatch-preserves branch (construct tag payload) = refl
