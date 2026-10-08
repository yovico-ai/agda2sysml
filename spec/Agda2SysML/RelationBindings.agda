{-# OPTIONS --safe #-}
module Agda2SysML.RelationBindings (Type : Set) (Meaning : Type → Set) where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda2SysML.Foundation using (trans; sym)

-- Contexts grow in telescope order. Every argument occupies a witness slot;
-- only an Abs codomain introduces a variable in the lexical context.
data Context : Set where
  empty : Context
  _▻_ : Context → Type → Context

data Values : Context → Set where
  none : Values empty
  snoc : ∀ {Γ t} → Values Γ → Meaning t → Values (Γ ▻ t)

data Variable (t : Type) : Context → Set where
  newest : ∀ {Γ} → Variable t (Γ ▻ t)
  older : ∀ {Γ u} → Variable t Γ → Variable t (Γ ▻ u)

lookup : ∀ {Γ t} → Variable t Γ → Values Γ → Meaning t
lookup newest (snoc env x) = x
lookup (older p) (snoc env x) = lookup p env

size : Context → Nat
size empty = zero
size (Γ ▻ t) = suc (size Γ)

-- Native witness numbers are absolute, starting at the oldest argument.
position : ∀ {Γ t} → Variable t Γ → Nat
position (newest {Γ}) = size Γ
position (older p) = position p

data Layout : Context → Context → Set where
  start : Layout empty empty
  bind : ∀ {runtime lexical t} → Layout runtime lexical
    → Layout (runtime ▻ t) (lexical ▻ t)
  nonbinding : ∀ {runtime lexical t} → Layout runtime lexical
    → Layout (runtime ▻ t) lexical

boundValues : ∀ {runtime lexical} → Layout runtime lexical → Values runtime → Values lexical
boundValues start none = none
boundValues (bind layout) (snoc env x) = snoc (boundValues layout env) x
boundValues (nonbinding layout) (snoc env x) = boundValues layout env

embed : ∀ {runtime lexical t} → Layout runtime lexical → Variable t lexical → Variable t runtime
embed (bind layout) newest = newest
embed (bind layout) (older p) = older (embed layout p)
embed (nonbinding layout) p = older (embed layout p)

lookup-preserves : ∀ {runtime lexical t} (layout : Layout runtime lexical)
  (p : Variable t lexical) (env : Values runtime)
  → lookup (embed layout p) env ≡ lookup p (boundValues layout env)
lookup-preserves (bind layout) newest (snoc env x) = refl
lookup-preserves (bind layout) (older p) (snoc env x) = lookup-preserves layout p env
lookup-preserves (nonbinding layout) p (snoc env x) = lookup-preserves layout p env

nonbinding-preserves-position : ∀ {runtime lexical t u}
  (layout : Layout runtime lexical) (p : Variable t lexical)
  → position (embed (nonbinding {t = u} layout) p) ≡ position (embed layout p)
nonbinding-preserves-position layout p = refl

new-binding-position : ∀ {runtime lexical t} (layout : Layout runtime lexical)
  → position (embed (bind {t = t} layout) newest) ≡ size runtime
new-binding-position layout = refl

data Endpoint (Γ : Context) (t : Type) : Set where
  literal : Meaning t → Endpoint Γ t
  reference : Variable t Γ → Endpoint Γ t

evaluate : ∀ {Γ t} → Endpoint Γ t → Values Γ → Meaning t
evaluate (literal x) env = x
evaluate (reference p) env = lookup p env

lower : ∀ {runtime lexical t} → Layout runtime lexical → Endpoint lexical t → Endpoint runtime t
lower layout (literal x) = literal x
lower layout (reference p) = reference (embed layout p)

endpoint-preserves : ∀ {runtime lexical t} (layout : Layout runtime lexical)
  (endpoint : Endpoint lexical t) (env : Values runtime)
  → evaluate (lower layout endpoint) env ≡ evaluate endpoint (boundValues layout env)
endpoint-preserves layout (literal x) env = refl
endpoint-preserves layout (reference p) env = lookup-preserves layout p env

-- Both directions preserve each endpoint equation used by Relations.emitRule.
-- No witness is removed, and unused witness values remain unconstrained.
equation-complete : ∀ {runtime lexical t} (layout : Layout runtime lexical)
  (endpoint : Endpoint lexical t) (env : Values runtime) (value : Meaning t)
  → evaluate endpoint (boundValues layout env) ≡ value
  → evaluate (lower layout endpoint) env ≡ value
equation-complete layout endpoint env value equation =
  trans (endpoint-preserves layout endpoint env) equation

equation-sound : ∀ {runtime lexical t} (layout : Layout runtime lexical)
  (endpoint : Endpoint lexical t) (env : Values runtime) (value : Meaning t)
  → evaluate (lower layout endpoint) env ≡ value
  → evaluate endpoint (boundValues layout env) ≡ value
equation-sound layout endpoint env value equation =
  trans (sym (endpoint-preserves layout endpoint env)) equation
