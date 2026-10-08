{-# OPTIONS --safe #-}
module Agda2SysML.CapturedIndices where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality
open import Agda2SysML.BooleanLowering using (Fin; first; next; Vec; []; _∷_; lookup)

-- Captured indices precede the original runtime telescope. Both injections
-- preserve lookup for every context size, value type and environment.
append : ∀ {A : Set} {c n} → Vec A c → Vec A n → Vec A (c + n)
append [] runtime = runtime
append (x ∷ captured) runtime = x ∷ append captured runtime

captureSlot : ∀ {c n} → Fin c → Fin (c + n)
captureSlot first = first
captureSlot (next i) = next (captureSlot i)

runtimeSlot : ∀ c {n} → Fin n → Fin (c + n)
runtimeSlot zero i = i
runtimeSlot (suc c) i = next (runtimeSlot c i)

capture-lookup : ∀ {A : Set} {c n} (captured : Vec A c)
  (runtime : Vec A n) (i : Fin c)
  → lookup (captureSlot i) (append captured runtime) ≡ lookup i captured
capture-lookup (x ∷ captured) runtime first = refl
capture-lookup (x ∷ captured) runtime (next i) = capture-lookup captured runtime i

runtime-lookup : ∀ {A : Set} {c n} (captured : Vec A c)
  (runtime : Vec A n) (i : Fin n)
  → lookup (runtimeSlot c i) (append captured runtime) ≡ lookup i runtime
runtime-lookup [] runtime i = refl
runtime-lookup (x ∷ captured) runtime i = runtime-lookup captured runtime i
