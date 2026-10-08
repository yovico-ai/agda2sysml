{-# OPTIONS --safe #-}
module Agda2SysML.SchemaConcatenation (Atom : Set) where

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (_++_; cong; trans; sym)
import Agda2SysML.SequenceValues as Values
open Values Atom using (Sequence; empty; prepend; encode; append-preserves)

-- A calculation is recognized by its two checked constructor equations,
-- rather than its name. These premises characterize all finite input lists.
characterize : (f : List Atom → List Atom → List Atom)
  → (∀ ys → f [] ys ≡ ys)
  → (∀ x xs ys → f (x ∷ xs) ys ≡ x ∷ f xs ys)
  → ∀ xs ys → f xs ys ≡ xs ++ ys
characterize f empty-case prepend-case [] ys = empty-case ys
characterize f empty-case prepend-case (x ∷ xs) ys =
  trans (prepend-case x xs ys)
    (cong (x ∷_) (characterize f empty-case prepend-case xs ys))

native-characterize : (f : Sequence → Sequence → Sequence)
  → (∀ ys → f empty ys ≡ ys)
  → (∀ x xs ys → f (prepend x xs) ys ≡ prepend x (f xs ys))
  → ∀ xs ys → f (encode xs) (encode ys) ≡ encode (xs ++ ys)
native-characterize f empty-case prepend-case [] ys = empty-case (encode ys)
native-characterize f empty-case prepend-case (x ∷ xs) ys =
  trans (prepend-case x (encode xs) (encode ys))
    (cong (prepend x) (native-characterize f empty-case prepend-case xs ys))

-- Flattening nested ordered concatenations changes grouping, never order,
-- length or the occurrence of a repeated atom.
associative : ∀ (xs ys zs : List Atom) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
associative [] ys zs = refl
associative (x ∷ xs) ys zs = cong (x ∷_) (associative xs ys zs)

module Correspondence
  (source : List Atom → List Atom → List Atom)
  (target : Sequence → Sequence → Sequence)
  (source-empty : ∀ ys → source [] ys ≡ ys)
  (source-prepend : ∀ x xs ys → source (x ∷ xs) ys ≡ x ∷ source xs ys)
  (target-empty : ∀ ys → target empty ys ≡ ys)
  (target-prepend : ∀ x xs ys → target (prepend x xs) ys ≡ prepend x (target xs ys)) where

  calculation-preserves : ∀ xs ys
    → target (encode xs) (encode ys) ≡ encode (source xs ys)
  calculation-preserves xs ys =
    trans (native-characterize target target-empty target-prepend xs ys)
      (sym (cong encode (characterize source source-empty source-prepend xs ys)))
