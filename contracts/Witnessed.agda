{-# OPTIONS --safe #-}
module Witnessed where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Indexed using (Phase)

-- Observational metadata is retained as witness data without changing the
-- state endpoints. Different constructors remain independent alternatives.
data Recorded : Bool → Bool → Set where
  keep : (before : Bool) → Bool → Recorded before before
  overwrite : Bool → (before : Bool) → Bool → (after : Bool) → Bool → Recorded before after
  classified : (before : Bool) → Phase → Recorded before before

source : ∀ {before after} → Recorded before after → Bool
source (keep before _) = before
source (overwrite _ before _ after _) = before
source (classified before _) = before

target : ∀ {before after} → Recorded before after → Bool
target (keep before _) = before
target (overwrite _ before _ after _) = after
target (classified before _) = before

source-preserves : ∀ {before after} (edge : Recorded before after) → source edge ≡ before
source-preserves (keep before _) = refl
source-preserves (overwrite _ before _ after _) = refl
source-preserves (classified before _) = refl

target-preserves : ∀ {before after} (edge : Recorded before after) → target edge ≡ after
target-preserves (keep before _) = refl
target-preserves (overwrite _ before _ after _) = refl
target-preserves (classified before _) = refl
