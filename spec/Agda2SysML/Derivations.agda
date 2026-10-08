{-# OPTIONS --safe #-}
module Agda2SysML.Derivations where

open import Agda2SysML.Foundation
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

shift-order : (offset : Nat) {a b : Nat} → a ≤ b → (offset + a) ≤ (offset + b)
shift-order zero proof = proof
shift-order (suc offset) proof = s≤s (shift-order offset proof)

-- Rule-generated material is explicit; attaching a checked derivation does
-- not manufacture an alignment to source syntax.
module Trace (Checked Rule Target Byte : Set) where
  data Origin : Set where
    checked : Checked → Origin
    generated : Rule → Origin

  record Derived (A : Set) : Set where
    constructor derived
    field
      origins : List Origin
      value : A
  open Derived public

  transform : {A B : Set} → (A → B) → Derived A → Derived B
  transform f (derived os x) = derived os (f x)

  combine : {A B C : Set} → (A → B → C) → Derived A → Derived B → Derived C
  combine f (derived xs x) (derived ys y) = derived (xs ++ ys) (f x y)

  composition-retains-inputs : {A B C : Set} (f : A → B → C)
    (x : Derived A) (y : Derived B)
    → origins (combine f x y) ≡ origins x ++ origins y
  composition-retains-inputs f x y = refl

  substitution-retains-origins : {A B : Set} (substitution : A → B) (x : Derived A)
    → origins (transform substitution x) ≡ origins x
  substitution-retains-origins substitution x = refl

  -- A newly constructed direct node starts with its checked evidence. Existing
  -- origins (including explicit boundaries) are retained when evidence is added.
  attach : {A : Set} → Checked → Derived A → Derived A
  attach c (derived os x) = derived (checked c ∷ os) x

  module Readiness (Aligned : Checked → Set) where
    data Ready : List Origin → Set where
      empty : Ready []
      input : ∀ {c os} → Aligned c → Ready os → Ready (checked c ∷ os)

    combine-ready : ∀ {xs ys} → Ready xs → Ready ys → Ready (xs ++ ys)
    combine-ready empty right = right
    combine-ready (input evidence left) right = input evidence (combine-ready left right)

    -- Readiness of a composition cannot hide an unavailable input on either
    -- side. In particular, adding checked evidence cannot discharge a boundary.
    ready-left : ∀ {xs} (ys : List Origin) → Ready (xs ++ ys) → Ready xs
    ready-left {[]} ys proof = empty
    ready-left {checked c ∷ xs} ys (input evidence proof) = input evidence (ready-left ys proof)
    ready-left {generated r ∷ xs} ys ()

    ready-right : (xs : List Origin) {ys : List Origin} → Ready (xs ++ ys) → Ready ys
    ready-right [] proof = proof
    ready-right (checked c ∷ xs) (input evidence proof) = ready-right xs proof
    ready-right (generated r ∷ xs) ()

    attach-retains-boundaries : {A : Set} (c : Checked) (x : Derived A)
      → Ready (origins (attach c x)) → Ready (origins x)
    attach-retains-boundaries c (derived os x) (input evidence proof) = proof

    generated-is-unavailable : (r : Rule) (os : List Origin)
      → Ready (generated r ∷ os) → Empty
    generated-is-unavailable r os ()

  -- Intervals describe the bytes emitted by a marked subtree, not a search
  -- for equal text. Concatenation shifts the right subtree's coordinates.
  record Span : Set where
    constructor span
    field
      identity : Target
      start end : Nat
  open Span

  shift : Nat → Span → Span
  shift n (span id a b) = span id (n + a) (n + b)

  shift-preserves-identity : (n : Nat) (s : Span)
    → identity (shift n s) ≡ identity s
  shift-preserves-identity n s = refl

  record Within (limit : Nat) (s : Span) : Set where
    constructor within
    field
      ordered : start s ≤ end s
      bounded : end s ≤ limit

  shift-preserves-bounds : (offset limit : Nat) (s : Span)
    → Within limit s → Within (offset + limit) (shift offset s)
  shift-preserves-bounds offset limit s (within ordered bounded) =
    within (shift-order offset ordered) (shift-order offset bounded)

  data Doc : Set where
    bytes : List Byte → Doc
    append : Doc → Doc → Doc
    mark : Target → Doc → Doc

  erase : Doc → List Byte
  erase (bytes xs) = xs
  erase (append a b) = erase a ++ erase b
  erase (mark _ d) = erase d

  length : List Byte → Nat
  length [] = zero
  length (_ ∷ xs) = suc (length xs)

  length-append : (xs ys : List Byte) → length (xs ++ ys) ≡ length xs + length ys
  length-append [] ys = refl
  length-append (x ∷ xs) ys = cong suc (length-append xs ys)

  size : Doc → Nat
  size (bytes xs) = length xs
  size (append a b) = size a + size b
  size (mark _ d) = size d

  measured-bytes : (d : Doc) → size d ≡ length (erase d)
  measured-bytes (bytes xs) = refl
  measured-bytes (append a b) = trans (cong (λ n → n + size b) (measured-bytes a))
    (trans (cong (λ n → length (erase a) + n) (measured-bytes b))
      (sym (length-append (erase a) (erase b))))
  measured-bytes (mark id d) = measured-bytes d

  mapMarks : (Target → Target) → Doc → Doc
  mapMarks f (bytes xs) = bytes xs
  mapMarks f (append a b) = append (mapMarks f a) (mapMarks f b)
  mapMarks f (mark id d) = mark (f id) (mapMarks f d)

  marks-preserve-bytes : (f : Target → Target) (d : Doc)
    → erase (mapMarks f d) ≡ erase d
  marks-preserve-bytes f (bytes xs) = refl
  marks-preserve-bytes f (append a b) = trans (cong (λ xs → xs ++ erase (mapMarks f b)) (marks-preserve-bytes f a))
    (cong (λ ys → erase a ++ ys) (marks-preserve-bytes f b))
  marks-preserve-bytes f (mark id d) = marks-preserve-bytes f d
