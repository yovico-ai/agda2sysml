{-# OPTIONS --safe #-}
module Agda2SysML.RecursiveValues (Tag Payload : Set) where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality

-- Finite constructor trees retain every ordered child and payload. A canonical
-- node count is generated metadata; it is not an additional source choice.
mutual
  data Tree : Set where
    node : Tag → Payload → Forest → Tree
  data Forest : Set where
    empty : Forest
    next : Tree → Forest → Forest

mutual
  count : Tree → Nat
  count (node tag payload children) = suc (counts children)
  counts : Forest → Nat
  counts empty = zero
  counts (next child rest) = count child + counts rest

mutual
  data NativeTree : Set where
    native-node : Tag → Payload → NativeForest → NativeTree
  data NativeForest : Set where
    native-empty : NativeForest
    native-next : NativeTree → NativeForest → NativeForest

mutual
  encode : Tree → NativeTree
  encode (node tag payload children) = native-node tag payload (encodeForest children)
  encodeForest : Forest → NativeForest
  encodeForest empty = native-empty
  encodeForest (next child rest) = native-next (encode child) (encodeForest rest)

mutual
  decode : NativeTree → Tree
  decode (native-node tag payload children) = node tag payload (decodeForest children)
  decodeForest : NativeForest → Forest
  decodeForest native-empty = empty
  decodeForest (native-next child rest) = next (decode child) (decodeForest rest)

mutual
  source-roundtrip : ∀ x → decode (encode x) ≡ x
  source-roundtrip (node tag payload children) rewrite forest-roundtrip children = refl
  forest-roundtrip : ∀ xs → decodeForest (encodeForest xs) ≡ xs
  forest-roundtrip empty = refl
  forest-roundtrip (next child rest) rewrite source-roundtrip child | forest-roundtrip rest = refl

mutual
  target-roundtrip : ∀ x → encode (decode x) ≡ x
  target-roundtrip (native-node tag payload children) rewrite native-forest-roundtrip children = refl
  native-forest-roundtrip : ∀ xs → encodeForest (decodeForest xs) ≡ xs
  native-forest-roundtrip native-empty = refl
  native-forest-roundtrip (native-next child rest) rewrite target-roundtrip child | native-forest-roundtrip rest = refl

nativeCount : NativeTree → Nat
nativeCount x = count (decode x)

count-preserves : ∀ x → nativeCount (encode x) ≡ count x
count-preserves x rewrite source-roundtrip x = refl

tag : Tree → Tag
tag (node t _ _) = t
payload : Tree → Payload
payload (node _ p _) = p

tag-preserves : ∀ x → tag (decode (encode x)) ≡ tag x
tag-preserves x rewrite source-roundtrip x = refl
payload-preserves : ∀ x → payload (decode (encode x)) ≡ payload x
payload-preserves x rewrite source-roundtrip x = refl

open import Agda2SysML.NaturalIndices using (_<_; zero-below; successor-below)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  zero-le : ∀ {n} → zero ≤ n
  successor-le : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step zero-le = zero-le
≤-step (successor-le bound) = successor-le (≤-step bound)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans zero-le _ = zero-le
≤-trans (successor-le first) (successor-le second) = successor-le (≤-trans first second)

left-bound : ∀ a b → a ≤ a + b
left-bound zero b = zero-le
left-bound (suc a) b = successor-le (left-bound a b)

right-bound : ∀ a b → b ≤ a + b
right-bound zero zero = zero-le
right-bound zero (suc b) = successor-le (right-bound zero b)
right-bound (suc a) b = ≤-step (right-bound a b)

strict-successor : ∀ {a b} → a ≤ b → a < (suc b)
strict-successor zero-le = zero-below
strict-successor (successor-le bound) = successor-below (strict-successor bound)

data Child (child : Tree) : Forest → Set where
  head : ∀ {rest} → Child child (next child rest)
  tail : ∀ {other rest} → Child child rest → Child child (next other rest)

child-sum-bound : ∀ {child children} → Child child children → count child ≤ counts children
child-sum-bound {child} head = left-bound (count child) _
child-sum-bound {children = next other rest} (tail membership) =
  ≤-trans (child-sum-bound membership) (right-bound (count other) (counts rest))

-- Every recursive edge decreases a finite natural. The emitted count equation
-- therefore excludes cycles, including cycles spread across mutual carriers.
child-decreases : ∀ {child children} (t : Tag) (p : Payload)
  → Child child children → count child < count (node t p children)
child-decreases t p membership = strict-successor (child-sum-bound membership)
