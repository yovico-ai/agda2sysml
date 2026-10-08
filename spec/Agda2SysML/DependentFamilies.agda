{-# OPTIONS --safe --without-K #-}
module Agda2SysML.DependentFamilies where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Agda.Builtin.Equality using (_≡_; refl)

-- A domain family is represented by its own carrier and index projection.
-- This is not a universal value representation shared by unrelated types.
module Family {ℓ ℓp : Level} (Index : Set ℓ) (Member : Index → Set ℓp) where
  Carrier : Set (ℓ ⊔ ℓp)
  Carrier = Σ Index Member

  Fibre : Index → Set (ℓ ⊔ ℓp)
  Fibre index = Σ Carrier (λ value → fst value ≡ index)

  encode : ∀ {index} → Member index → Fibre index
  encode {index} value = (index , value) , refl

  decode : ∀ {index} → Fibre index → Member index
  decode ((index , value) , refl) = value

  decode-encode : ∀ {index} (value : Member index) → decode (encode value) ≡ value
  decode-encode value = refl

  encode-decode : ∀ {index} (value : Fibre index) → encode (decode value) ≡ value
  encode-decode ((index , member) , refl) = refl
