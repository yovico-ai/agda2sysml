{-# OPTIONS --safe --without-K #-}
module Agda2SysML.DependencyScope (Name Value : Set) where

open import Agda.Builtin.List
open import Agda.Builtin.Equality

mutual
  data Term : Set where
    literal : Value → Term
    call : Name → Args → Term
  data Args : Set where
    none : Args
    next : Term → Args → Args

Table : Set
Table = Name → List Value → Value

mutual
  evaluate : Table → Term → Value
  evaluate table (literal v) = v
  evaluate table (call name args) = table name (evaluateArgs table args)
  evaluateArgs : Table → Args → List Value
  evaluateArgs table none = []
  evaluateArgs table (next term rest) = evaluate table term ∷ evaluateArgs table rest

mutual
  data Uses (name : Name) : Term → Set where
    callee : ∀ {args} → Uses name (call name args)
    argument : ∀ {other args} → UsesArgs name args → Uses name (call other args)
  data UsesArgs (name : Name) : Args → Set where
    first : ∀ {term rest} → Uses name term → UsesArgs name (next term rest)
    later : ∀ {term rest} → UsesArgs name rest → UsesArgs name (next term rest)

Agrees : Table → Table → Term → Set
Agrees left right term = ∀ name → Uses name term → ∀ args → left name args ≡ right name args

mutual
  footprint-sufficient : ∀ {left right} (term : Term) → Agrees left right term
    → evaluate left term ≡ evaluate right term
  footprint-sufficient (literal v) agree = refl
  footprint-sufficient {left} {right} (call name args) agree
    rewrite args-sufficient args (λ n use → agree n (argument use)) = agree name callee _

  args-sufficient : ∀ {left right} (args : Args)
    → (∀ name → UsesArgs name args → ∀ values → left name values ≡ right name values)
    → evaluateArgs left args ≡ evaluateArgs right args
  args-sufficient none agree = refl
  args-sufficient (next term rest) agree
    rewrite footprint-sufficient term (λ name use → agree name (first use))
          | args-sufficient rest (λ name use → agree name (later use)) = refl

-- A reduction must first establish equality with the checked source result.
-- Footprint exclusion alone cannot justify a source transformation. Recursive
-- call-table compatibility is supplied by RecursiveCalls' accessibility law.
reduced-footprint-preserves : (sourceResult : Value) (reduced : Term)
  (source target : Table) → sourceResult ≡ evaluate source reduced
  → Agrees source target reduced → sourceResult ≡ evaluate target reduced
reduced-footprint-preserves sourceResult reduced source target refl agreement =
  footprint-sufficient reduced agreement
