{-# OPTIONS --safe #-}
module Agda2SysML.Mapping where

open import Agda2SysML.Foundation

data Role : Set where
  state-type command-type transition-function transition-relation
    state-projection invariant theorem : Role

-- Fits includes the resolved signature and the other roles' shared typing
-- context. This core is invoked after adapter applicability is established;
-- unsupported signatures are not classified as incompatible. The decision
-- procedure is a frontend obligation, not an axiom.
module Validation (Symbol : Set) (Fits : Role → Symbol → Set)
  (check : (role : Role) (symbol : Symbol) → Dec (Fits role symbol)) where

  data Acceptance (role : Role) : List Symbol → Set where
    unique-compatible : {symbol : Symbol} → Fits role symbol
      → Acceptance role (symbol ∷ [])

  data Refusal (role : Role) : List Symbol → Set where
    unresolved : Refusal role []
    ambiguous : (first second : Symbol) (rest : List Symbol)
      → Refusal role (first ∷ second ∷ rest)
    incompatible : {symbol : Symbol} → (Fits role symbol → Empty)
      → Refusal role (symbol ∷ [])

  data Result (role : Role) (candidates : List Symbol) : Set where
    accepted : Acceptance role candidates → Result role candidates
    refused : Refusal role candidates → Result role candidates

  validate : (role : Role) (candidates : List Symbol) → Result role candidates
  validate role [] = refused unresolved
  validate role (symbol ∷ []) with check role symbol
  ... | yes proof = accepted (unique-compatible proof)
  ... | no refute = refused (incompatible refute)
  validate role (first ∷ second ∷ rest) = refused (ambiguous first second rest)

  acceptance-excludes-refusal : {role : Role} {candidates : List Symbol}
    → Acceptance role candidates → Refusal role candidates → Empty
  acceptance-excludes-refusal (unique-compatible proof) (incompatible refute) = refute proof

  accepted-symbol-fits : {role : Role} {candidates : List Symbol}
    → Acceptance role candidates → (symbol : Symbol)
    → (candidate-equality : candidates ≡ symbol ∷ []) → Fits role symbol
  accepted-symbol-fits (unique-compatible proof) symbol refl = proof

  data IsAccepted {role : Role} {candidates : List Symbol}
    : Result role candidates → Set where
    success : {proof : Acceptance role candidates} → IsAccepted (accepted proof)

  validate-accepts-compatible : (role : Role) (symbol : Symbol)
    → Fits role symbol → IsAccepted (validate role (symbol ∷ []))
  validate-accepts-compatible role symbol proof with check role symbol
  ... | yes witness = success
  ... | no refute = absurd (refute proof)
