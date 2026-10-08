{-# OPTIONS --safe #-}
module Agda2SysML.UniverseLevels where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; Empty)

maximum : Nat → Nat → Nat
maximum zero n = n
maximum (suc n) zero = suc n
maximum (suc n) (suc m) = suc (maximum n m)

-- The supported closed level fragment; no runtime level values are modeled.
data Expression (Parameter : Set) : Set where
  parameter : Parameter → Expression Parameter
  constant : Nat → Expression Parameter
  successor : Expression Parameter → Expression Parameter
  join : Expression Parameter → Expression Parameter → Expression Parameter

evaluate : ∀ {P} → (P → Nat) → Expression P → Nat
evaluate env (parameter p) = env p
evaluate env (constant n) = n
evaluate env (successor x) = suc (evaluate env x)
evaluate env (join x y) = maximum (evaluate env x) (evaluate env y)

substitute : ∀ {P Q} → (P → Expression Q) → Expression P → Expression Q
substitute replacement (parameter p) = replacement p
substitute replacement (constant n) = constant n
substitute replacement (successor x) = successor (substitute replacement x)
substitute replacement (join x y) = join (substitute replacement x) (substitute replacement y)

substitution-preserves : ∀ {P Q} (replacement : P → Expression Q) (env : Q → Nat) (x : Expression P)
  → evaluate env (substitute replacement x) ≡ evaluate (λ p → evaluate env (replacement p)) x
substitution-preserves replacement env (parameter p) = refl
substitution-preserves replacement env (constant n) = refl
substitution-preserves replacement env (successor x) = cong suc (substitution-preserves replacement env x)
substitution-preserves replacement env (join x y)
  rewrite substitution-preserves replacement env x | substitution-preserves replacement env y = refl

closed : Empty → Nat
closed ()

resolve : ∀ {P} → (P → Nat) → Expression P → Expression Empty
resolve env x = constant (evaluate env x)

resolution-exact : ∀ {P} (env : P → Nat) (x : Expression P)
  → evaluate closed (resolve env x) ≡ evaluate env x
resolution-exact env x = refl

-- Equal concrete levels have one resolved key, independent of expression shape.
resolution-canonical : ∀ {P Q} (left : P → Nat) (right : Q → Nat) x y
  → evaluate left x ≡ evaluate right y → resolve left x ≡ resolve right y
resolution-canonical left right x y equality = cong constant equality

module Runtime (Type : Set) (Meaning : Type → Set) where
  data Slot : Set where
    level : Nat → Slot
    value : Type → Slot

  data Environment : List Slot → Set where
    empty : Environment []
    static : ∀ {slots} (n : Nat) → Environment slots → Environment (level n ∷ slots)
    dynamic : ∀ {slots t} → Meaning t → Environment slots → Environment (value t ∷ slots)

  runtimeTypes : List Slot → List Type
  runtimeTypes [] = []
  runtimeTypes (level n ∷ slots) = runtimeTypes slots
  runtimeTypes (value t ∷ slots) = t ∷ runtimeTypes slots

  data Values : List Type → Set where
    nil : Values []
    cons : ∀ {ts t} → Meaning t → Values ts → Values (t ∷ ts)

  erase : ∀ {slots} → Environment slots → Values (runtimeTypes slots)
  erase empty = nil
  erase (static n env) = erase env
  erase (dynamic x env) = cons x (erase env)

  restore : (slots : List Slot) → Values (runtimeTypes slots) → Environment slots
  restore [] nil = empty
  restore (level n ∷ slots) xs = static n (restore slots xs)
  restore (value t ∷ slots) (cons x xs) = dynamic x (restore slots xs)

  environment-roundtrip : ∀ {slots} (env : Environment slots) → restore slots (erase env) ≡ env
  environment-roundtrip empty = refl
  environment-roundtrip (static n env) = cong (static n) (environment-roundtrip env)
  environment-roundtrip (dynamic x env) = cong (dynamic x) (environment-roundtrip env)

  data Position (t : Type) : List Slot → Set where
    here : ∀ {slots} → Position t (value t ∷ slots)
    skipLevel : ∀ {slots n} → Position t slots → Position t (level n ∷ slots)
    skipValue : ∀ {slots u} → Position t slots → Position t (value u ∷ slots)

  data Index (t : Type) : List Type → Set where
    first : ∀ {ts} → Index t (t ∷ ts)
    next : ∀ {ts u} → Index t ts → Index t (u ∷ ts)

  lower : ∀ {t slots} → Position t slots → Index t (runtimeTypes slots)
  lower here = first
  lower (skipLevel p) = lower p
  lower (skipValue p) = next (lower p)

  lookup : ∀ {t slots} → Position t slots → Environment slots → Meaning t
  lookup here (dynamic x env) = x
  lookup (skipLevel p) (static n env) = lookup p env
  lookup (skipValue p) (dynamic x env) = lookup p env

  nativeLookup : ∀ {t ts} → Index t ts → Values ts → Meaning t
  nativeLookup first (cons x xs) = x
  nativeLookup (next p) (cons x xs) = nativeLookup p xs

  lookup-preserves : ∀ {t slots} (p : Position t slots) (env : Environment slots)
    → nativeLookup (lower p) (erase env) ≡ lookup p env
  lookup-preserves here (dynamic x env) = refl
  lookup-preserves (skipLevel p) (static n env) = lookup-preserves p env
  lookup-preserves (skipValue p) (dynamic x env) = lookup-preserves p env
