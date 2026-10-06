{-# OPTIONS --safe #-}
module Agda2SysML.Resolution where

open import Agda2SysML.Foundation

-- The frontend supplies canonical candidate declarations after Agda scope
-- resolution. Duplicate paths to the same declaration must be coalesced there.
data Resolution (Symbol : Set) : Set where
  missing : Resolution Symbol
  resolved : Symbol → Resolution Symbol
  ambiguous : Symbol → Symbol → List Symbol → Resolution Symbol

resolve : {Symbol : Set} → List Symbol → Resolution Symbol
resolve [] = missing
resolve (symbol ∷ []) = resolved symbol
resolve (first ∷ second ∷ rest) = ambiguous first second rest

-- A successful selection is possible exactly for a singleton candidate list.
resolved-exactly-one : {Symbol : Set} (candidates : List Symbol) (symbol : Symbol)
  → resolve candidates ≡ resolved symbol → candidates ≡ symbol ∷ []
resolved-exactly-one [] symbol ()
resolved-exactly-one (candidate ∷ []) symbol refl = refl
resolved-exactly-one (first ∷ second ∷ rest) symbol ()

singleton-resolves : {Symbol : Set} (symbol : Symbol)
  → resolve (symbol ∷ []) ≡ resolved symbol
singleton-resolves symbol = refl

missing-exactly-empty : {Symbol : Set} (candidates : List Symbol)
  → resolve candidates ≡ missing → candidates ≡ []
missing-exactly-empty [] proof = refl
missing-exactly-empty (symbol ∷ []) ()
missing-exactly-empty (first ∷ second ∷ rest) ()
