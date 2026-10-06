{-# OPTIONS --safe #-}
module Agda2SysML.Terms where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong)

-- Intrinsically typed semantic syntax. A source adapter must justify the
-- interpretation of each local reference; these are not arbitrary compiler
-- terms admitted without a correspondence obligation.
data Term {ℓ : Level} (Context : Set ℓ)
  : (Type : Context → Set ℓ) → ((context : Context) → Type context)
  → Set (lsuc ℓ) where
  local : {Type : Context → Set ℓ} (lookup : (context : Context) → Type context)
    → Term Context Type lookup
  constant : {Type : Set ℓ} (value : Type)
    → Term Context (λ _ → Type) (λ _ → value)
  application : {Domain : Context → Set ℓ}
    {Codomain : (context : Context) → Domain context → Set ℓ}
    {function : (context : Context) → (argument : Domain context) → Codomain context argument}
    {argument : (context : Context) → Domain context}
    → Term Context (λ context → (value : Domain context) → Codomain context value) function
    → Term Context Domain argument
    → Term Context (λ context → Codomain context (argument context))
      (λ context → function context (argument context))
  abstraction : {Domain : Context → Set ℓ} {Codomain : Σ Context Domain → Set ℓ}
    {body : (extended : Σ Context Domain) → Codomain extended}
    → Term (Σ Context Domain) Codomain body
    → Term Context (λ context → (value : Domain context) → Codomain (context , value))
      (λ context value → body (context , value))
  binding : {Domain : Context → Set ℓ} {value : (context : Context) → Domain context}
    {Codomain : Σ Context Domain → Set ℓ}
    {body : (extended : Σ Context Domain) → Codomain extended}
    → Term Context Domain value → Term (Σ Context Domain) Codomain body
    → Term Context (λ context → Codomain (context , value context))
      (λ context → body (context , value context))

lift : {ℓ : Level} {Context Other : Set ℓ} {Domain : Context → Set ℓ}
  → (environment : Other → Context)
  → Σ Other (λ other → Domain (environment other)) → Σ Context Domain
lift environment (context , value) = environment context , value

reindex : {ℓ : Level} {Context Other : Set ℓ} {Type : Context → Set ℓ}
  {value : (context : Context) → Type context}
  → (environment : Other → Context) → Term Context Type value
  → Term Other (λ other → Type (environment other)) (λ other → value (environment other))
reindex environment (local lookup) = local (λ other → lookup (environment other))
reindex environment (constant value) = constant value
reindex environment (application function argument) =
  application (reindex environment function) (reindex environment argument)
reindex environment (abstraction body) =
  abstraction (reindex (lift environment) body)
reindex environment (binding value body) =
  binding (reindex environment value)
    (reindex (lift environment) body)

data Shape : Set where
  reference literal : Shape
  apply let-bind : Shape → Shape → Shape
  lambda : Shape → Shape

shape : {ℓ : Level} {Context : Set ℓ} {Type : Context → Set ℓ}
  {value : (context : Context) → Type context} → Term Context Type value → Shape
shape (local lookup) = reference
shape (constant value) = literal
shape (application function argument) = apply (shape function) (shape argument)
shape (abstraction body) = lambda (shape body)
shape (binding value body) = let-bind (shape value) (shape body)

-- Environment substitution preserves dependent typing by the type of reindex;
-- it also preserves syntax structure, including binders, without capture.
reindex-preserves-shape : {ℓ : Level} {Context Other : Set ℓ}
  {Type : Context → Set ℓ} {value : (context : Context) → Type context}
  (environment : Other → Context) (term : Term Context Type value)
  → shape (reindex environment term) ≡ shape term
reindex-preserves-shape environment (local lookup) = refl
reindex-preserves-shape environment (constant value) = refl
reindex-preserves-shape environment (application function argument)
  rewrite reindex-preserves-shape environment function
  | reindex-preserves-shape environment argument = refl
reindex-preserves-shape environment (abstraction body)
  = cong lambda (reindex-preserves-shape (lift environment) body)
reindex-preserves-shape environment (binding value body)
  rewrite reindex-preserves-shape environment value
  | reindex-preserves-shape (lift environment) body = refl
