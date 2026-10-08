{-# OPTIONS --safe #-}
module Agda2SysML.FamilyRelations where

open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; subst; sym)

-- A relation row retains the index and the complete native payload. Relation
-- membership is evidence about that payload, never a replacement for it.
record Binding (Index Payload : Set) (Source : Index → Set) : Set₁ where
  field
    member : Index → Payload → Set
    encode : ∀ {index} → Source index → Payload
    admitted : ∀ {index} (x : Source index) → member index (encode x)
    decode : ∀ {index} (p : Payload) → member index p → Source index
    source-roundtrip : ∀ {index} (x : Source index)
      → decode (encode x) (admitted x) ≡ x
    payload-roundtrip : ∀ {index} p membership
      → encode (decode {index} p membership) ≡ p

module Transport {Index Payload : Set} {Source : Index → Set}
  (binding : Binding Index Payload Source) where
  open Binding binding

  record Row : Set where
    constructor row
    field
      index : Index
      payload : Payload
      membership : member index payload

  record At (expected : Index) : Set where
    constructor at
    field
      value : Row
      index-equality : Row.index value ≡ expected

  encodeAt : ∀ {index} → Source index → At index
  encodeAt {index} x = at (row index (encode x) (admitted x)) refl

  decodeAt : ∀ {index} → At index → Source index
  decodeAt (at (row _ p membership) refl) = decode p membership

  index-preserves : ∀ {index} (x : Source index)
    → Row.index (At.value (encodeAt x)) ≡ index
  index-preserves x = refl

  source-roundtrip-at : ∀ {index} (x : Source index)
    → decodeAt (encodeAt x) ≡ x
  source-roundtrip-at x = source-roundtrip x

  payload-roundtrip-at : ∀ {index} (x : At index)
    → Row.payload (At.value (encodeAt (decodeAt x))) ≡ Row.payload (At.value x)
  payload-roundtrip-at (at (row _ p membership) refl) = payload-roundtrip p membership

  -- No equality of membership witnesses is assumed: proof-relevant payload
  -- distinctions remain covered by both round-trip laws above.
  select : ∀ {index} → At index → Payload
  select x = Row.payload (At.value x)

  selection-preserves : ∀ {index} (x : Source index)
    → select (encodeAt x) ≡ encode x
  selection-preserves x = refl

  wrap : ∀ {index} → Source index → At index
  wrap = encodeAt

  wrapping-preserves : ∀ {index} (x : Source index)
    → decodeAt (wrap x) ≡ x
  wrapping-preserves x = source-roundtrip x

  -- Transport across an actual index equality. Mere payload equality cannot
  -- be used to change an index or to identify distinct family bindings.
  reindex : ∀ {i j} → i ≡ j → At i → At j
  reindex refl x = x

  reindex-payload-preserves : ∀ {i j} (equal : i ≡ j) (x : At i)
    → select (reindex equal x) ≡ select x
  reindex-payload-preserves refl x = refl
