{-# OPTIONS --safe #-}
module Agda2SysML.Coverage where

open import Agda2SysML.Foundation

-- Evidence is supplied by a particular checked translation rule. Choosing a
-- trivial proposition does not establish correspondence; the adapter must discharge the
-- actual per-definition obligation described in the written specification.
module Inventory (Id Reason : Set) (Evidence : Id → Set) where

  data Entry (id : Id) : Set where
    translated : Evidence id → Entry id
    textual : Reason → Entry id

  data Report : List Id → Set where
    empty : Report []
    entry : {id : Id} {ids : List Id} → Entry id → Report ids → Report (id ∷ ids)

  sources : {ids : List Id} → Report ids → List Id
  sources empty = []
  sources (entry {id} item rest) = id ∷ sources rest

  no-silent-omissions : {ids : List Id} (report : Report ids) → sources report ≡ ids
  no-silent-omissions empty = refl
  no-silent-omissions (entry {id} item rest) = cong (λ ids → id ∷ ids) (no-silent-omissions rest)

  data AllTranslated : {ids : List Id} → Report ids → Set where
    done : AllTranslated empty
    next : {id : Id} {ids : List Id} {evidence : Evidence id} {rest : Report ids}
      → AllTranslated rest → AllTranslated (entry (translated evidence) rest)

  data HasTextual : {ids : List Id} → Report ids → Set where
    at-head : {id : Id} {ids : List Id} {reason : Reason} {rest : Report ids}
      → HasTextual (entry {id} (textual reason) rest)
    in-tail : {id : Id} {ids : List Id} {item : Entry id} {rest : Report ids}
      → HasTextual rest → HasTextual (entry item rest)

  complete-excludes-textual : {ids : List Id} {report : Report ids}
    → AllTranslated report → HasTextual report → Empty
  complete-excludes-textual done ()
  complete-excludes-textual (next rest) (in-tail fallback) = complete-excludes-textual rest fallback

  classify : {ids : List Id} (report : Report ids) → Dec (AllTranslated report)
  classify empty = yes done
  classify (entry (textual reason) rest) = no (λ ())
  classify (entry (translated evidence) rest) with classify rest
  ... | yes proof = yes (next proof)
  ... | no refute = no (λ { (next proof) → refute proof })

  record Complete {ids : List Id} (report : Report ids) : Set where
    constructor complete
    field
      evidence : AllTranslated report

  strict : {ids : List Id} (report : Report ids) → Maybe (Complete report)
  strict report with classify report
  ... | yes proof = just (complete proof)
  ... | no refute = nothing

  strict-accepts-complete : {ids : List Id} (report : Report ids)
    → AllTranslated report → IsJust (strict report)
  strict-accepts-complete report proof with classify report
  ... | yes witness = present
  ... | no refute = absurd (refute proof)

  strict-refuses-textual : {ids : List Id} (report : Report ids)
    → HasTextual report → strict report ≡ nothing
  strict-refuses-textual report fallback with classify report
  ... | yes proof = absurd (complete-excludes-textual proof fallback)
  ... | no refute = refl
