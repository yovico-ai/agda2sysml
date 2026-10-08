{-# OPTIONS --safe --without-K #-}
module Agda2SysML.DependentSums where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda2SysML.DependentFamilies

-- Each constructor has its own preceding payload tuple and dependent member.
-- Prefix can itself be a dependent tuple, so this law composes along an ordered
-- telescope. Inactive optional slots belong to the AlgebraicValues encoding.
module Constructors {ℓt ℓp ℓi ℓm : Level} (Tag : Set ℓt)
  (Prefix : Tag → Set ℓp) (Index : Tag → Set ℓi)
  (index : (tag : Tag) → Prefix tag → Index tag)
  (Member : (tag : Tag) → Index tag → Set ℓm) where

  Payload : Tag → Set (ℓp ⊔ ℓm)
  Payload tag = Σ (Prefix tag) (λ prefix → Member tag (index tag prefix))

  NativePayload : Tag → Set (ℓp ⊔ ℓi ⊔ ℓm)
  NativePayload tag = Σ (Prefix tag)
    (λ prefix → Family.Fibre (Index tag) (Member tag) (index tag prefix))

  Source : Set (ℓt ⊔ ℓp ⊔ ℓm)
  Source = Σ Tag Payload

  Native : Set (ℓt ⊔ ℓp ⊔ ℓi ⊔ ℓm)
  Native = Σ Tag NativePayload

  encode : Source → Native
  encode (tag , prefix , member) =
    tag , prefix , Family.encode (Index tag) (Member tag) member

  decode : Native → Source
  decode (tag , prefix , member) =
    tag , prefix , Family.decode (Index tag) (Member tag) member

  source-roundtrip : (value : Source) → decode (encode value) ≡ value
  source-roundtrip (tag , prefix , member) = refl

  target-roundtrip : (value : Native) → encode (decode value) ≡ value
  target-roundtrip (tag , prefix , member)
    rewrite Family.encode-decode (Index tag) (Member tag) member = refl

  tag-preserves : (value : Source) → fst (encode value) ≡ fst value
  tag-preserves (tag , prefix , member) = refl

  member-index-preserves : (tag : Tag) (prefix : Prefix tag)
    (member : Member tag (index tag prefix))
    → fst (fst (snd (snd (encode (tag , prefix , member))))) ≡ index tag prefix
  member-index-preserves tag prefix member = refl

  dispatch : ∀ {ℓr} {Result : Set ℓr}
    → ((tag : Tag) → Payload tag → Result) → Native → Result
  dispatch branch value = branch (fst (decode value)) (snd (decode value))

  dispatch-preserves : ∀ {ℓr} {Result : Set ℓr}
    (branch : (tag : Tag) → Payload tag → Result) (value : Source)
    → dispatch branch (encode value) ≡ branch (fst value) (snd value)
  dispatch-preserves branch (tag , prefix , member) = refl

  -- The result index may depend on any admitted payload. Preserving payload
  -- observation also preserves the enclosing family's constructor result index.
  result-index-preserves : ∀ {ℓr} {ResultIndex : Set ℓr}
    (resultIndex : (tag : Tag) → Payload tag → ResultIndex) (value : Source)
    → dispatch resultIndex (encode value) ≡ resultIndex (fst value) (snd value)
  result-index-preserves = dispatch-preserves

  native : (Source → Source) → Native → Native
  native operation value = encode (operation (decode value))

  operation-preserves : (operation : Source → Source) (value : Source)
    → native operation (encode value) ≡ encode (operation value)
  operation-preserves operation (tag , prefix , member) = refl
