{-# OPTIONS --safe --without-K #-}
module Agda2SysML.DependentRecords where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda2SysML.DependentFamilies

-- Keep the contradiction type local to this --without-K module.
data Empty : Set where

-- Prefix may contain any number of preceding fields. Index can be a tuple of
-- finite domains; the native adapter checks the actual ordered projections.
module Record {ℓp ℓi ℓm : Level} (Prefix : Set ℓp) (Index : Set ℓi)
  (index : Prefix → Index) (Member : Index → Set ℓm) where
  module F = Family Index Member

  Source : Set (ℓp ⊔ ℓm)
  Source = Σ Prefix (λ prefix → Member (index prefix))

  Native : Set (ℓp ⊔ ℓi ⊔ ℓm)
  Native = Σ Prefix (λ prefix → F.Fibre (index prefix))

  encode : Source → Native
  encode (prefix , member) = prefix , F.encode member

  decode : Native → Source
  decode (prefix , member) = prefix , F.decode member

  decode-encode : (value : Source) → decode (encode value) ≡ value
  decode-encode (prefix , member) = refl

  encode-decode : (value : Native) → encode (decode value) ≡ value
  encode-decode (prefix , member) rewrite F.encode-decode member = refl

  prefix-preserves : (value : Source) → fst (encode value) ≡ fst value
  prefix-preserves (prefix , member) = refl

  field-preserves : (prefix : Prefix) (member : Member (index prefix))
    → F.decode (snd (encode (prefix , member))) ≡ member
  field-preserves prefix member = F.decode-encode member

  native : (Source → Source) → Native → Native
  native operation value = encode (operation (decode value))

  operation-preserves : (operation : Source → Source) (value : Source)
    → native operation (encode value) ≡ encode (operation value)
  operation-preserves operation value = refl

  -- The emitted input constraint compares the member's stored index with the
  -- index selected from preceding inputs. It is exactly the missing evidence
  -- when the dependent fibre is represented by an unconstrained carrier.
  RawInput : Set (ℓp ⊔ ℓi ⊔ ℓm)
  RawInput = Σ Prefix (λ _ → F.Carrier)

  InputContract : RawInput → Set ℓi
  InputContract (prefix , carrier) = fst carrier ≡ index prefix

  forgetInput : Native → RawInput
  forgetInput (prefix , carrier , proof) = prefix , carrier

  input-contract-required : (value : Native) → InputContract (forgetInput value)
  input-contract-required (prefix , carrier , proof) = proof

  admitInput : (value : RawInput) → InputContract value → Native
  admitInput (prefix , carrier) proof = prefix , carrier , proof

  input-contract-sufficient : (value : RawInput) (proof : InputContract value)
    → forgetInput (admitInput value proof) ≡ value
  input-contract-sufficient (prefix , carrier) proof = refl

  input-contract-roundtrip : (value : Native)
    → admitInput (forgetInput value) (input-contract-required value) ≡ value
  input-contract-roundtrip (prefix , carrier , proof) = refl

  input-contract-refuses-mismatch : (raw : RawInput)
    → (InputContract raw → Empty) → (value : Native)
    → forgetInput value ≡ raw → Empty
  input-contract-refuses-mismatch raw mismatch value refl = mismatch (input-contract-required value)

-- A projected index is sound only when the checked receiver denotes the same
-- preceding input as the source receiver. No equality of receiver types alone
-- supplies this evidence.
module ProjectedInput {ℓp ℓr ℓi ℓm : Level}
  (Prefix : Set ℓp) (Receiver : Set ℓr) (Index : Set ℓi)
  (receiver checkedReceiver : Prefix → Receiver)
  (project : Receiver → Index) (Member : Index → Set ℓm)
  (sameReceiver : (prefix : Prefix) → checkedReceiver prefix ≡ receiver prefix) where
  module Input = Record Prefix Index (λ prefix → project (receiver prefix)) Member

  CheckedContract : Input.RawInput → Set ℓi
  CheckedContract (prefix , carrier) = fst carrier ≡ project (checkedReceiver prefix)

  projected-index-preserves : (prefix : Prefix)
    → project (checkedReceiver prefix) ≡ project (receiver prefix)
  projected-index-preserves prefix rewrite sameReceiver prefix = refl

  contract-forward : (raw : Input.RawInput) → CheckedContract raw → Input.InputContract raw
  contract-forward (prefix , carrier) proof rewrite sameReceiver prefix = proof

  contract-backward : (raw : Input.RawInput) → Input.InputContract raw → CheckedContract raw
  contract-backward (prefix , carrier) proof rewrite sameReceiver prefix = proof

  admission-preserves : (raw : Input.RawInput) (proof : CheckedContract raw)
    → Input.forgetInput (Input.admitInput raw (contract-forward raw proof)) ≡ raw
  admission-preserves raw proof = Input.input-contract-sufficient raw (contract-forward raw proof)

  refuses-projected-mismatch : (raw : Input.RawInput)
    → (CheckedContract raw → Empty) → (value : Input.Native)
    → Input.forgetInput value ≡ raw → Empty
  refuses-projected-mismatch raw mismatch value equality =
    Input.input-contract-refuses-mismatch raw
      (λ proof → mismatch (contract-backward raw proof)) value equality
