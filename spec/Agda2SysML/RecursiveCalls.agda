{-# OPTIONS --safe --without-K #-}
module Agda2SysML.RecursiveCalls
  (Call : Set) (_≺_ : Call → Call → Set)
  (Source Target : Call → Set)
  (encode : ∀ {c} → Source c → Target c) where

open import Agda.Builtin.Equality

-- A call includes the function identity and its ordered actual arguments, so
-- this theorem also covers mutual recursion. Accessibility must come from
-- checked termination; a cyclic call graph alone is not a termination proof.
data Accessible (c : Call) : Set where
  accessible : (∀ d → d ≺ c → Accessible d) → Accessible c

SourceStep : Set
SourceStep = ∀ c → (∀ d → d ≺ c → Source d) → Source c

TargetStep : Set
TargetStep = ∀ c → (∀ d → d ≺ c → Target d) → Target c

module Preservation (sourceStep : SourceStep) (targetStep : TargetStep)
  (step-preserves : ∀ c sourceCalls targetCalls
    → (∀ d (smaller : d ≺ c) → targetCalls d smaller ≡ encode (sourceCalls d smaller))
    → targetStep c targetCalls ≡ encode (sourceStep c sourceCalls)) where

  source : ∀ c → Accessible c → Source c
  source c (accessible earlier) = sourceStep c (λ d smaller → source d (earlier d smaller))

  target : ∀ c → Accessible c → Target c
  target c (accessible earlier) = targetStep c (λ d smaller → target d (earlier d smaller))

  recursive-calls-preserve : ∀ c (termination : Accessible c)
    → target c termination ≡ encode (source c termination)
  recursive-calls-preserve c (accessible earlier) = step-preserves c
    (λ d smaller → source d (earlier d smaller))
    (λ d smaller → target d (earlier d smaller))
    (λ d smaller → recursive-calls-preserve d (earlier d smaller))
