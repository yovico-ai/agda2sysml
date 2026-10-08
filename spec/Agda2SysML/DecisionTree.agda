{-# OPTIONS --safe #-}
module Agda2SysML.DecisionTree where

open import Agda2SysML.Foundation

-- Input contains the command, initial state and any explicit context.
-- Output retains the whole observable outcome, including refusal reasons.
data Tree (Input Output : Set) : Set where
  leaf : (Input → Output) → Tree Input Output
  branch : (Input → Bool) → Tree Input Output → Tree Input Output
    → Tree Input Output

evaluate : {I O : Set} → Tree I O → I → O
evaluate (leaf result) input = result input
evaluate (branch predicate positive negative) input with predicate input
... | true = evaluate positive input
... | false = evaluate negative input

record Rule (Input Output : Set) : Set where
  constructor rule
  field
    guard : Input → Bool
    effect : Input → Output
open Rule public

restrict : {I O : Set} → (I → Bool) → List (Rule I O) → List (Rule I O)
restrict predicate [] = []
restrict predicate (rule guard effect ∷ rest) =
  rule (λ input → predicate input ∧ guard input) effect ∷ restrict predicate rest

select : {I O : Set} → List (Rule I O) → I → Maybe O
select [] input = nothing
select (rule guard effect ∷ rest) input with guard input
... | true = just (effect input)
... | false = select rest input

normalize : {I O : Set} → Tree I O → List (Rule I O)
normalize (leaf result) = rule (λ _ → true) result ∷ []
normalize (branch predicate positive negative) =
  restrict predicate (normalize positive) ++
  restrict (λ input → not (predicate input)) (normalize negative)

select-append : {I O : Set} (left right : List (Rule I O)) (input : I)
  → select (left ++ right) input ≡ orElse (select left input) (select right input)
select-append [] right input = refl
select-append (rule guard effect ∷ rest) right input with guard input
... | true = refl
... | false = select-append rest right input

restrict-true : {I O : Set} (predicate : I → Bool)
  (rules : List (Rule I O)) (input : I)
  → predicate input ≡ true → select (restrict predicate rules) input ≡ select rules input
restrict-true predicate [] input proof = refl
restrict-true predicate (rule guard effect ∷ rest) input proof
  rewrite proof with guard input
... | true = refl
... | false = restrict-true predicate rest input proof

restrict-false : {I O : Set} (predicate : I → Bool)
  (rules : List (Rule I O)) (input : I)
  → predicate input ≡ false → select (restrict predicate rules) input ≡ nothing
restrict-false predicate [] input proof = refl
restrict-false predicate (rule guard effect ∷ rest) input proof
  rewrite proof = restrict-false predicate rest input proof

-- General semantic preservation, including refusal priority and full effects.
normalization-preserves-evaluation : {I O : Set} (tree : Tree I O) (input : I)
  → select (normalize tree) input ≡ just (evaluate tree input)
normalization-preserves-evaluation (leaf result) input = refl
normalization-preserves-evaluation (branch predicate positive negative) input
  with predicate input in choice
... | true
  rewrite select-append (restrict predicate (normalize positive))
    (restrict (λ x → not (predicate x)) (normalize negative)) input
  | restrict-true predicate (normalize positive) input choice
  | normalization-preserves-evaluation positive input = refl
... | false
  rewrite select-append (restrict predicate (normalize positive))
    (restrict (λ x → not (predicate x)) (normalize negative)) input
  | restrict-false predicate (normalize positive) input choice
  | restrict-true (λ x → not (predicate x)) (normalize negative) input (cong not choice)
  | normalization-preserves-evaluation negative input = refl

normalization-sound : {I O : Set} (tree : Tree I O) (input : I) (output : O)
  → select (normalize tree) input ≡ just output → evaluate tree input ≡ output
normalization-sound tree input output selected =
  just-injective (trans (sym (normalization-preserves-evaluation tree input)) selected)

-- Any property of the complete original outcome transfers to the selected one.
normalization-preserves-contract : {I O : Set} (tree : Tree I O)
  (Contract : I → O → Set)
  → ((input : I) → Contract input (evaluate tree input))
  → (input : I) (output : O)
  → select (normalize tree) input ≡ just output → Contract input output
normalization-preserves-contract tree Contract established input output selected =
  subst (Contract input) (normalization-sound tree input output selected) (established input)

-- Compiled pattern matching may backtrack to a fallback outside a nested
-- split. Keep that fallback in its original input environment.
data PartialTree (Input Output : Set) : Set where
  miss : PartialTree Input Output
  yield : (Input → Output) → PartialTree Input Output
  test : (Input → Bool) → PartialTree Input Output → PartialTree Input Output
    → PartialTree Input Output

evaluatePartial : ∀ {I O} → PartialTree I O → I → Maybe O
evaluatePartial miss input = nothing
evaluatePartial (yield result) input = just (result input)
evaluatePartial (test guard positive negative) input with guard input
... | true = evaluatePartial positive input
... | false = evaluatePartial negative input

withFallback : ∀ {I O} → PartialTree I O → Tree I O → Tree I O
withFallback miss fallback = fallback
withFallback (yield result) fallback = leaf result
withFallback (test guard positive negative) fallback =
  branch guard (withFallback positive fallback) (withFallback negative fallback)

fallback-preserves : ∀ {I O} (tree : PartialTree I O)
  (fallback : Tree I O) (input : I)
  → just (evaluate (withFallback tree fallback) input)
    ≡ orElse (evaluatePartial tree input) (just (evaluate fallback input))
fallback-preserves miss fallback input = refl
fallback-preserves (yield result) fallback input = refl
fallback-preserves (test guard positive negative) fallback input with guard input
... | true = fallback-preserves positive fallback input
... | false = fallback-preserves negative fallback input
