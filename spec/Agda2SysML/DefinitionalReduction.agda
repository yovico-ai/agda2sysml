{-# OPTIONS --safe --without-K #-}
module Agda2SysML.DefinitionalReduction where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

-- These reductions are equalities of computations. No equality between
-- arbitrary proofs, inhabitants, or record fields is assumed.
beta : ∀ {ℓ} {Γ : Set ℓ} {A : Γ → Set ℓ}
  {B : Σ Γ A → Set ℓ} (body : (p : Σ Γ A) → B p)
  (argument : (γ : Γ) → A γ) (γ : Γ)
  → (λ x → body (γ , x)) (argument γ) ≡ body (γ , argument γ)
beta body argument γ = refl

project-first : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
  (value : A) (evidence : B value) → fst {B = B} (value , evidence) ≡ value
project-first value evidence = refl

project-second : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ}
  (value : A) (evidence : B value) → snd {B = B} (value , evidence) ≡ evidence
project-second value evidence = refl

-- Any finite adapter reduction chain must provide equality for every step.
-- Exhausting a reduction budget permits refusal, never an assumed equality.
module Chains {ℓ} (Syntax Value : Set ℓ) (meaning : Syntax → Value)
  (Step : Syntax → Syntax → Set ℓ)
  (step-preserves : ∀ {before after} → Step before after
    → meaning before ≡ meaning after) where
  data Reduces : Syntax → Syntax → Set ℓ where
    stop : ∀ {term} → Reduces term term
    next : ∀ {before middle after} → Step before middle
      → Reduces middle after → Reduces before after

  reduction-preserves : ∀ {before after} → Reduces before after
    → meaning before ≡ meaning after
  reduction-preserves stop = refl
  reduction-preserves (next step rest) =
    trans (step-preserves step) (reduction-preserves rest)

-- A closure retains every captured runtime value. Specialization removes only
-- the function argument; captured values remain explicit calculation inputs.
closure-specialization : ∀ {ℓ} {Capture A B Result : Set ℓ}
  (helper : (A → B) → Result) (body : Capture → A → B)
  (captured : Capture)
  → (λ environment → helper (body environment)) captured
    ≡ helper (body captured)
closure-specialization helper body captured = refl

record-field-computation : ∀ {ℓ} {Γ A : Set ℓ} {B : A → Set ℓ}
  (first : Γ → A) (second : (γ : Γ) → B (first γ)) (γ : Γ)
  → _≡_ {A = Σ A B}
    (fst {B = B} (first γ , second γ) , snd {B = B} (first γ , second γ))
    (first γ , second γ)
record-field-computation first second γ = refl
