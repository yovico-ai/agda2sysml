{-# OPTIONS --safe #-}
module Agda2SysML.SourceOccurrences where

open import Agda2SysML.Foundation
open import Agda.Builtin.Nat using (Nat)

-- Coordinates and shared payloads never identify syntax occurrences.
module Catalog (Module Owner Location Payload : Set) where
  record Key : Set where
    constructor key
    field
      source-module : Module
      path : List Nat

  record Occurrence : Set where
    constructor occurrence
    field
      identity : Key
      owner : Maybe Owner
      location : Location
      payload : Payload

  resolve : List Owner → Maybe Owner
  resolve (x ∷ []) = just x
  resolve _ = nothing

  resolved-is-unique : (candidates : List Owner) (x : Owner)
    → resolve candidates ≡ just x → candidates ≡ (x ∷ [])
  resolved-is-unique [] x ()
  resolved-is-unique (y ∷ []) x proof = cong (λ y → y ∷ []) (just-injective proof)
  resolved-is-unique (y ∷ z ∷ rest) x ()

  relocate : (Location → Location) → Occurrence → Occurrence
  relocate f (occurrence k owner loc value) = occurrence k owner (f loc) value

  relocation-preserves-identity : (f : Location → Location) (item : Occurrence)
    → Occurrence.identity (relocate f item) ≡ Occurrence.identity item
  relocation-preserves-identity f item = refl

  relocation-preserves-owner : (f : Location → Location) (item : Occurrence)
    → Occurrence.owner (relocate f item) ≡ Occurrence.owner item
  relocation-preserves-owner f item = refl

  relocateAll : (Location → Location) → List Occurrence → List Occurrence
  relocateAll f [] = []
  relocateAll f (x ∷ xs) = relocate f x ∷ relocateAll f xs

  identities : List Occurrence → List Key
  identities [] = []
  identities (x ∷ xs) = Occurrence.identity x ∷ identities xs

  catalog-identities-preserved : (f : Location → Location) (items : List Occurrence)
    → identities (relocateAll f items) ≡ identities items
  catalog-identities-preserved f [] = refl
  catalog-identities-preserved f (x ∷ xs) = cong (λ ys → Occurrence.identity x ∷ ys) (catalog-identities-preserved f xs)

  repack : (Payload → Payload) → Occurrence → Occurrence
  repack f (occurrence k owner loc value) = occurrence k owner loc (f value)

  repacking-preserves-distinction : (f : Payload → Payload) (a b : Occurrence)
    → (Occurrence.identity a ≡ Occurrence.identity b → Empty)
    → Occurrence.identity (repack f a) ≡ Occurrence.identity (repack f b) → Empty
  repacking-preserves-distinction f a b distinct equal = distinct equal
