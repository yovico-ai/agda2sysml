{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; _⊔_)

module Relational {ℓ ℓp : Level}
  (State : Set ℓ) (permitted : State → Set ℓp) (advance : State → State) where

-- Alternatives describe admissible edges without imposing a priority order.
data Step : State → State → Set (ℓ ⊔ ℓp) where
  stay : ∀ before → Step before before
  move : ∀ before → permitted before → Step before (advance before)

reflexive : ∀ state → Step state state
reflexive = stay

preserves : ∀ {ℓi} (Invariant : State → Set ℓi)
  → (∀ state → permitted state → Invariant state → Invariant (advance state))
  → ∀ {before after} → Step before after → Invariant before → Invariant after
preserves Invariant advance-preserves (stay before) invariant = invariant
preserves Invariant advance-preserves (move before permission) invariant =
  advance-preserves before permission invariant
