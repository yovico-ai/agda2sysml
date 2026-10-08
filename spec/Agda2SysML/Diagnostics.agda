{-# OPTIONS --safe #-}
module Agda2SysML.Diagnostics where

open import Agda2SysML.Foundation
import Agda2SysML.Coverage as Coverage

data Category : Set where
  unsupported-syntax unsupported-semantics unsupported-target-representation : Category

-- Classification decorates a refusal; its original explanation and links
-- remain available verbatim. It supplies no translation evidence.
module Located (Source Model Message : Set) where
  record Reason : Set where
    constructor reason
    field
      source : Source
      models : List Model
      message : Message

  record Classified : Set where
    constructor classified
    field
      original : Reason
      category : Category

  annotate : (Reason → Category) → Reason → Classified
  annotate classify r = classified r (classify r)

  annotation-preserves-links : (classify : Reason → Category) (r : Reason)
    → Classified.original (annotate classify r) ≡ r
  annotation-preserves-links classify r = refl

-- Reason transformations cannot change required identities, evidence, or
-- completeness. This includes adding categories and aggregating rule causes.
module Accounting (Id A B : Set) (Evidence : Id → Set) (f : A → B) where
  module Before = Coverage.Inventory Id A Evidence
  module After = Coverage.Inventory Id B Evidence

  mapEntry : {id : Id} → Before.Entry id → After.Entry id
  mapEntry (Before.translated evidence) = After.translated evidence
  mapEntry (Before.textual reason) = After.textual (f reason)

  mapReport : {ids : List Id} → Before.Report ids → After.Report ids
  mapReport Before.empty = After.empty
  mapReport (Before.entry item rest) = After.entry (mapEntry item) (mapReport rest)

  preserves-identities : {ids : List Id} (report : Before.Report ids)
    → After.sources (mapReport report) ≡ Before.sources report
  preserves-identities Before.empty = refl
  preserves-identities (Before.entry {id} item rest) =
    cong (λ ids → id ∷ ids) (preserves-identities rest)

  preserves-complete : {ids : List Id} (report : Before.Report ids)
    → Before.AllTranslated report → After.AllTranslated (mapReport report)
  preserves-complete Before.empty Before.done = After.done
  preserves-complete (Before.entry (Before.translated evidence) rest) (Before.next proof) = After.next (preserves-complete rest proof)

  reflects-complete : {ids : List Id} (report : Before.Report ids)
    → After.AllTranslated (mapReport report) → Before.AllTranslated report
  reflects-complete Before.empty After.done = Before.done
  reflects-complete (Before.entry (Before.translated evidence) rest) (After.next proof) = Before.next (reflects-complete rest proof)
  reflects-complete (Before.entry (Before.textual reason) rest) ()

  preserves-refusal : {ids : List Id} (report : Before.Report ids)
    → Before.HasTextual report → After.HasTextual (mapReport report)
  preserves-refusal (Before.entry (Before.textual reason) rest) Before.at-head = After.at-head
  preserves-refusal (Before.entry item rest) (Before.in-tail proof) = After.in-tail (preserves-refusal rest proof)

  strict-still-refuses : {ids : List Id} (report : Before.Report ids)
    → Before.HasTextual report → After.strict (mapReport report) ≡ nothing
  strict-still-refuses report proof = After.strict-refuses-textual (mapReport report) (preserves-refusal report proof)

  -- Coverage arithmetic is also unchanged, not merely the complete/incomplete
  -- flag. The required count is fixed by the shared list of identities.
  open import Agda.Builtin.Nat using (Nat; zero; suc)

  before-count : {ids : List Id} → Before.Report ids → Nat
  before-count Before.empty = zero
  before-count (Before.entry (Before.translated evidence) rest) = suc (before-count rest)
  before-count (Before.entry (Before.textual reason) rest) = before-count rest

  after-count : {ids : List Id} → After.Report ids → Nat
  after-count After.empty = zero
  after-count (After.entry (After.translated evidence) rest) = suc (after-count rest)
  after-count (After.entry (After.textual reason) rest) = after-count rest

  preserves-discharged-count : {ids : List Id} (report : Before.Report ids)
    → after-count (mapReport report) ≡ before-count report
  preserves-discharged-count Before.empty = refl
  preserves-discharged-count (Before.entry (Before.translated evidence) rest) = cong suc (preserves-discharged-count rest)
  preserves-discharged-count (Before.entry (Before.textual reason) rest) = preserves-discharged-count rest
