{-# OPTIONS --safe #-}
open import Agda.Builtin.Equality
module Agda2SysML.StructuredIndices
  (Source Target : Set)
  (encodeAtom : Source → Target) (decodeAtom : Target → Source)
  (atom-source-roundtrip : ∀ x → decodeAtom (encodeAtom x) ≡ x)
  (atom-target-roundtrip : ∀ x → encodeAtom (decodeAtom x) ≡ x) where

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; trans; sym; subst)

-- Structured indices retain every element, position and repeated occurrence.
-- These laws quantify over arbitrary atom carriers, not a chosen finite domain.
encodeIndex : List Source → List Target
encodeIndex [] = []
encodeIndex (x ∷ xs) = encodeAtom x ∷ encodeIndex xs

decodeIndex : List Target → List Source
decodeIndex [] = []
decodeIndex (x ∷ xs) = decodeAtom x ∷ decodeIndex xs

index-source-roundtrip : ∀ xs → decodeIndex (encodeIndex xs) ≡ xs
index-source-roundtrip [] = refl
index-source-roundtrip (x ∷ xs)
  rewrite atom-source-roundtrip x | index-source-roundtrip xs = refl

index-target-roundtrip : ∀ xs → encodeIndex (decodeIndex xs) ≡ xs
index-target-roundtrip [] = refl
index-target-roundtrip (x ∷ xs)
  rewrite atom-target-roundtrip x | index-target-roundtrip xs = refl

index-equality-preserves : ∀ {xs ys} → xs ≡ ys → encodeIndex xs ≡ encodeIndex ys
index-equality-preserves equality = cong encodeIndex equality

index-equality-reflects : ∀ {xs ys} → encodeIndex xs ≡ encodeIndex ys → xs ≡ ys
index-equality-reflects {xs} {ys} equality =
  trans (sym (index-source-roundtrip xs))
    (trans (cong decodeIndex equality) (index-source-roundtrip ys))

transport-inverse : ∀ {A : Set} (P : A → Set) {x y}
  (equality : x ≡ y) (member : P y)
  → subst P equality (subst P (sym equality) member) ≡ member
transport-inverse P refl member = refl

-- A native fibre is indexed by the decoded schema. Transport changes only the
-- index representation and preserves the complete dependent member.
module Fibre (Member : List Source → Set) where
  NativeMember : List Target → Set
  NativeMember schema = Member (decodeIndex schema)

  encodeMember : ∀ {schema} → Member schema → NativeMember (encodeIndex schema)
  encodeMember {schema} member = subst Member (sym (index-source-roundtrip schema)) member

  decodeMember : ∀ {schema} → NativeMember (encodeIndex schema) → Member schema
  decodeMember {schema} member = subst Member (index-source-roundtrip schema) member

  member-roundtrip : ∀ {schema} (member : Member schema)
    → decodeMember (encodeMember member) ≡ member
  member-roundtrip {schema} member =
    transport-inverse Member (index-source-roundtrip schema) member
