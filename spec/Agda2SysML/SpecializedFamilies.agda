{-# OPTIONS --safe --without-K #-}
module Agda2SysML.SpecializedFamilies where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda2SysML.DependentFamilies

-- Static denotes the interpreted concrete type/universe argument tuple.
-- Its equality comes from static substitution/resolution, never from erasing
-- runtime indices. Prefix includes every preceding record field in order.
module Instantiation {ℓs ℓi ℓm ℓp : Level}
  (Static : Set ℓs) (Index : Set ℓi) (Member : Static → Index → Set ℓm)
  (Prefix : Set ℓp) (index : Prefix → Index) where

  Source : Static → Set (ℓp ⊔ ℓm)
  Source key = Σ Prefix (λ prefix → Member key (index prefix))

  Native : Static → Set (ℓp ⊔ ℓi ⊔ ℓm)
  Native key = Σ Prefix (λ prefix → Family.Fibre Index (Member key) (index prefix))

  encode : ∀ {source target} → source ≡ target → Source source → Native target
  encode {target = target} refl (prefix , member) =
    prefix , Family.encode Index (Member target) member

  decode : ∀ {source target} → source ≡ target → Native target → Source source
  decode {source = source} refl (prefix , member) =
    prefix , Family.decode Index (Member source) member

  source-roundtrip : ∀ {source target} (same : source ≡ target) (value : Source source)
    → decode same (encode same value) ≡ value
  source-roundtrip refl (prefix , member) = refl

  target-roundtrip : ∀ {source target} (same : source ≡ target) (value : Native target)
    → encode same (decode same value) ≡ value
  target-roundtrip {target = target} refl (prefix , member)
    rewrite Family.encode-decode Index (Member target) member = refl

  index-preserves : ∀ {source target} (same : source ≡ target) (value : Source source)
    → fst (fst (snd (encode same value))) ≡ index (fst value)
  index-preserves refl (prefix , member) = refl

  specialize : ∀ {source target} → source ≡ target
    → (Source source → Source source) → Native target → Native target
  specialize same operation value = encode same (operation (decode same value))

  operation-preserves : ∀ {source target} (same : source ≡ target)
    (operation : Source source → Source source) (value : Source source)
    → specialize same operation (encode same value) ≡ encode same (operation value)
  operation-preserves refl operation (prefix , member) = refl
