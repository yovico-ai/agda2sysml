{-# OPTIONS --safe --without-K #-}
module Agda2SysML.SequenceValues {a} (A : Set a) where

open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality

-- Native ordered, nonunique, finite sequences. Constructor order and repeated
-- elements are retained. An unordered set is not an implementation of this
-- carrier. The renderer constrains sequence size to exclude infinity.
data Sequence : Set a where
  empty : Sequence
  prepend : A → Sequence → Sequence

encode : List A → Sequence
encode [] = empty
encode (x ∷ xs) = prepend x (encode xs)

decode : Sequence → List A
decode empty = []
decode (prepend x xs) = x ∷ decode xs

source-roundtrip : ∀ xs → decode (encode xs) ≡ xs
source-roundtrip [] = refl
source-roundtrip (x ∷ xs) rewrite source-roundtrip xs = refl

target-roundtrip : ∀ xs → encode (decode xs) ≡ xs
target-roundtrip empty = refl
target-roundtrip (prepend x xs) rewrite target-roundtrip xs = refl

length : List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

size : Sequence → Nat
size empty = zero
size (prepend _ xs) = suc (size xs)

length-preserves : ∀ xs → size (encode xs) ≡ length xs
length-preserves [] = refl
length-preserves (_ ∷ xs) rewrite length-preserves xs = refl

caseList : ∀ {b} {B : Set b} → B → (A → List A → B) → List A → B
caseList z s [] = z
caseList z s (x ∷ xs) = s x xs

caseSequence : ∀ {b} {B : Set b} → B → (A → Sequence → B) → Sequence → B
caseSequence z s empty = z
caseSequence z s (prepend x xs) = s x xs

case-preserves : ∀ {b} {B : Set b} (z : B) s xs
  → caseSequence z (λ x rest → s x (decode rest)) (encode xs) ≡ caseList z s xs
case-preserves z s [] = refl
case-preserves z s (x ∷ xs) rewrite source-roundtrip xs = refl

append : Sequence → Sequence → Sequence
append empty ys = ys
append (prepend x xs) ys = prepend x (append xs ys)

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

append-preserves : ∀ xs ys → encode (xs ++ ys) ≡ append (encode xs) (encode ys)
append-preserves [] ys = refl
append-preserves (x ∷ xs) ys rewrite append-preserves xs ys = refl
