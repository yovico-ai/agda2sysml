{-# OPTIONS --safe #-}
module Agda2SysML.Relations where

open import Agda2SysML.Foundation

-- Witnesses represent constructor arguments, including implicit indices and
-- evidence premises. A relation need not be decidable or deterministic.
record RelationRule (State : Set) : Set₁ where
  constructor relation-rule
  field
    Witness : Set
    before : Witness → State
    after : Witness → State
    premises : Witness → Set
open RelationRule public

data Permits {S : Set} (r : RelationRule S) (source target : S) : Set where
  permitted : (w : Witness r) → before r w ≡ source → after r w ≡ target
    → premises r w → Permits r source target

data Related {S : Set} : List (RelationRule S) → S → S → Set₁ where
  first : {r : RelationRule S} {rs : List (RelationRule S)} {s t : S}
    → Permits r s t → Related (r ∷ rs) s t
  later : {r : RelationRule S} {rs : List (RelationRule S)} {s t : S}
    → Related rs s t → Related (r ∷ rs) s t

-- Output constraints retain the witness and both endpoint equations. These
-- are semantic constraints, not a claim that arbitrary Agda is SysML syntax.
record Edge (State : Set) : Set₁ where
  constructor edge
  field
    Parameter : Set
    constraint : State → State → Parameter → Set
open Edge public

record EndpointConditions {S : Set} (r : RelationRule S)
  (source target : S) (w : Witness r) : Set where
  constructor conditions
  field
    source-matches : before r w ≡ source
    target-matches : after r w ≡ target
    admitted : premises r w

emitRule : {S : Set} → RelationRule S → Edge S
emitRule r = edge (Witness r) (EndpointConditions r)

data Connected {S : Set} : List (Edge S) → S → S → Set₁ where
  here : {e : Edge S} {es : List (Edge S)} {s t : S}
    → (parameter : Parameter e) → constraint e s t parameter → Connected (e ∷ es) s t
  there : {e : Edge S} {es : List (Edge S)} {s t : S}
    → Connected es s t → Connected (e ∷ es) s t

emit : {S : Set} → List (RelationRule S) → List (Edge S)
emit [] = []
emit (r ∷ rs) = emitRule r ∷ emit rs

relation-complete : {S : Set} (rules : List (RelationRule S)) {s t : S}
  → Related rules s t → Connected (emit rules) s t
relation-complete (r ∷ rs) (first (permitted w source target proof)) =
  here w (conditions source target proof)
relation-complete (r ∷ rs) (later proof) = there (relation-complete rs proof)

relation-sound : {S : Set} (rules : List (RelationRule S)) {s t : S}
  → Connected (emit rules) s t → Related rules s t
relation-sound [] ()
relation-sound (r ∷ rs) (here w (conditions source target proof)) =
  first (permitted w source target proof)
relation-sound (r ∷ rs) (there proof) = later (relation-sound rs proof)
