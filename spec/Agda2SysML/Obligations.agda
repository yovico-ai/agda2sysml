{-# OPTIONS --safe #-}
module Agda2SysML.Obligations where

open import Agda2SysML.Foundation

data Kind : Set where
  structure behavior statement proof-source reduction-source external-assumption : Kind

-- These predicates are instantiated with source/target correspondence, exact
-- statement/source retention, and declared assumption provenance respectively.
module Requirements (Id : Set)
  (Structural Behavioral Statement ProofSource ReducedSource Assumption : Id → Set) where

  data Evidence (id : Id) : Kind → Set where
    structural : Structural id → Evidence id structure
    semantic : Behavioral id → Evidence id behavior
    statement-preserved : Statement id → Evidence id statement
    proof-retained : ProofSource id → Evidence id proof-source
    -- ReducedSource must establish checked semantics-preserving preparation,
    -- exclusion from the complete prepared dependency graph, and source
    -- retention. It is not a proof-irrelevance or translation claim for id.
    reduction-source-retained : ReducedSource id → Evidence id reduction-source
    assumption-declared : Assumption id → Evidence id external-assumption

  behavior-requires-semantics : {id : Id} → Evidence id behavior → Behavioral id
  behavior-requires-semantics (semantic proof) = proof

  statement-requires-preservation : {id : Id} → Evidence id statement → Statement id
  statement-requires-preservation (statement-preserved proof) = proof

  -- A textual proof body satisfies its own obligation without asserting behavior.
  retained-proof-is-admissible : {id : Id} → ProofSource id → Evidence id proof-source
  retained-proof-is-admissible = proof-retained

  data Obligation : Set where
    require : Id → Kind → Obligation

  Discharged : Obligation → Set
  Discharged (require id kind) = Evidence id kind

  -- List membership retains which exact requirement a completion discharges.
  data Member (obligation : Obligation) : List Obligation → Set where
    here : {rest : List Obligation} → Member obligation (obligation ∷ rest)
    there : {head : Obligation} {rest : List Obligation}
      → Member obligation rest → Member obligation (head ∷ rest)

  data Complete : List Obligation → Set where
    empty : Complete []
    next : {obligation : Obligation} {rest : List Obligation}
      → Discharged obligation → Complete rest → Complete (obligation ∷ rest)

  completion-discharges-every-member : {obligation : Obligation} {all : List Obligation}
    → Complete all → Member obligation all → Discharged obligation
  completion-discharges-every-member (next proof rest) here = proof
  completion-discharges-every-member (next proof rest) (there member) =
    completion-discharges-every-member rest member

  complete-behavior-is-semantic : {id : Id} {all : List Obligation}
    → Complete all → Member (require id behavior) all → Behavioral id
  complete-behavior-is-semantic completion member =
    behavior-requires-semantics (completion-discharges-every-member completion member)
