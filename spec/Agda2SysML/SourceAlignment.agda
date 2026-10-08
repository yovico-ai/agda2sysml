{-# OPTIONS --safe #-}
module Agda2SysML.SourceAlignment where

open import Agda2SysML.Foundation
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- This models the admitted direct fragment, not Agda's whole elaborator.
-- Source names have already been resolved by the compiler. The adapter must
-- supply the binding and canonical-name evidence used by this relation.
module Direct (Symbol Binder : Set) where
  data Source : Set where
    var : Binder → Source
    global : Symbol → Source
    apply : Source → Source → Source

  data Checked : Set where
    var : Nat → Checked
    global : Symbol → Checked
    apply : Checked → Checked → Checked

  Environment = Binder → Maybe Nat

  data Align (env : Environment) : Source → Checked → Set where
    bound : ∀ {b n} → env b ≡ just n → Align env (var b) (var n)
    named : ∀ {s} → Align env (global s) (global s)
    application : ∀ {f x g y} → Align env f g → Align env x y
      → Align env (apply f x) (apply g y)

  mapMaybe : (Nat → Nat) → Maybe Nat → Maybe Nat
  mapMaybe f nothing = nothing
  mapMaybe f (just n) = just (f n)

  rename : (Nat → Nat) → Checked → Checked
  rename f (var n) = var (f n)
  rename f (global s) = global s
  rename f (apply g x) = apply (rename f g) (rename f x)

  -- A verified clause-to-leaf binder permutation transports alignment.
  -- Nothing here allows constructing a permutation from var spellings.
  rename-alignment : ∀ {env source checked} (f : Nat → Nat)
    → Align env source checked
    → Align (λ b → mapMaybe f (env b)) source (rename f checked)
  rename-alignment f (bound evidence) = bound (cong (mapMaybe f) evidence)
  rename-alignment f named = named
  rename-alignment f (application function argument) =
    application (rename-alignment f function) (rename-alignment f argument)

  -- Candidate selection consumes proven alignments. Uniqueness alone is not
  -- evidence of alignment, and ambiguous evidence cannot produce exactness.
  select : ∀ {env source checked} → List (Align env source checked)
    → Maybe (Align env source checked)
  select (proof ∷ []) = just proof
  select _ = nothing

  exact-requires-evidence : ∀ {env source checked}
    (candidates : List (Align env source checked)) (proof : Align env source checked)
    → select candidates ≡ just proof → candidates ≡ (proof ∷ [])
  exact-requires-evidence [] proof ()
  exact-requires-evidence (p ∷ []) proof evidence = cong (λ p → p ∷ []) (just-injective evidence)
  exact-requires-evidence (p ∷ q ∷ rest) proof ()

  ambiguous-is-unavailable : ∀ {env source checked}
    (p q : Align env source checked) (rest : List (Align env source checked))
    → select (p ∷ q ∷ rest) ≡ nothing
  ambiguous-is-unavailable p q rest = refl

  -- Signature preparation may replace NoAbs with Abs. Resolve de Bruijn
  -- references to absolute telescope slots before comparing the types.
  mapChecked : (Nat → Checked) → Maybe Nat → Maybe Checked
  mapChecked f nothing = nothing
  mapChecked f (just n) = just (f n)

  applyChecked : Maybe Checked → Maybe Checked → Maybe Checked
  applyChecked (just f) (just x) = just (apply f x)
  applyChecked _ _ = nothing

  resolve : (Nat → Maybe Nat) → Checked → Maybe Checked
  resolve env (var n) = mapChecked var (env n)
  resolve env (global s) = just (global s)
  resolve env (apply f x) = applyChecked (resolve env f) (resolve env x)

  -- Arbitrary rebasing is sound only with evidence that each moved reference
  -- still resolves to the same slot. Equality of raw indices is insufficient.
  resolve-renaming : (before after : Nat → Maybe Nat) (f : Nat → Nat)
    → ((n : Nat) → after (f n) ≡ before n)
    → (term : Checked) → resolve after (rename f term) ≡ resolve before term
  resolve-renaming before after f agrees (var n) = cong (mapChecked var) (agrees n)
  resolve-renaming before after f agrees (global s) = refl
  resolve-renaming before after f agrees (apply g x) =
    trans (cong (λ left → applyChecked left (resolve after (rename f x)))
      (resolve-renaming before after f agrees g))
      (cong (applyChecked (resolve before g)) (resolve-renaming before after f agrees x))

  lookup : List Nat → Nat → Maybe Nat
  lookup [] n = nothing
  lookup (slot ∷ rest) zero = just slot
  lookup (slot ∷ rest) (suc n) = lookup rest n

  unused-binder-preserves-resolution : (slot : Nat) (env : List Nat) (term : Checked)
    → resolve (lookup (slot ∷ env)) (rename suc term) ≡ resolve (lookup env) term
  unused-binder-preserves-resolution slot env term =
    resolve-renaming (lookup env) (lookup (slot ∷ env)) suc (λ n → refl) term

-- Explicit prefix projections in constructor signatures correspond to a
-- checked postfix elimination on a resolved binder. Admissible supplies the
-- compiler's proper-projection evidence; spelling is never that evidence.
module Projection (Symbol Binder Value : Set)
  (Admissible : Symbol → Set) (projectValue : Symbol → Value → Value) where

  record Source : Set where
    constructor prefix
    field
      projection : Symbol
      receiver : Binder

  record Checked : Set where
    constructor postfix
    field
      receiver : Nat
      projection : Symbol

  data Align (env : Binder → Maybe Nat) : Source → Checked → Set where
    projected : ∀ {symbol binder index}
      → Admissible symbol → env binder ≡ just index
      → Align env (prefix symbol binder) (postfix index symbol)

  applyField : Symbol → (Nat → Value) → Maybe Nat → Maybe Value
  applyField symbol values nothing = nothing
  applyField symbol values (just index) = just (projectValue symbol (values index))

  sourceMeaning : (Binder → Maybe Nat) → (Nat → Value) → Source → Maybe Value
  sourceMeaning env values (prefix symbol binder) = applyField symbol values (env binder)

  checkedMeaning : (Nat → Value) → Checked → Maybe Value
  checkedMeaning values (postfix index symbol) = just (projectValue symbol (values index))

  projection-preserves : ∀ {env source checked}
    → Align env source checked → (values : Nat → Value)
    → sourceMeaning env values source ≡ checkedMeaning values checked
  projection-preserves (projected {symbol = symbol} proper binding) values =
    cong (applyField symbol values) binding

  -- Preparation may rebase the receiver but must retain both the canonical
  -- projection and the resolved value. This holds for every index map.
  rebase : (Nat → Nat) → Checked → Checked
  rebase f (postfix index symbol) = postfix (f index) symbol

  rebase-preserves : (before after : Nat → Value) (f : Nat → Nat)
    → ((index : Nat) → after (f index) ≡ before index)
    → (term : Checked) → checkedMeaning after (rebase f term) ≡ checkedMeaning before term
  rebase-preserves before after f agrees (postfix index symbol) =
    cong (λ value → just (projectValue symbol value)) (agrees index)
