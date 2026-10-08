{-# OPTIONS --safe #-}
module Agda2SysML.OpenParameters where

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda2SysML.Foundation using (cong; _++_; orElse)
open import Agda2SysML.Resolution using (Resolution; missing; resolved; ambiguous; resolve)

-- A native type extent represents a source parameter only with a justified
-- carrier correspondence. Member denotes native extent membership. The ≈
-- relation denotes equal extents (mutual inclusion), independent of ordering.
-- No finiteness assumption is imposed on the extent or source carrier.
record Binding (Source Native Classifier : Set)
  (Member : Classifier → Native → Set) : Set₁ where
  field
    _≈_ : Classifier → Classifier → Set
    same : ∀ c → c ≈ c
    same-members : ∀ {a b} → a ≈ b → ∀ x → Member a x → Member b x
    classifier : Classifier
    encode : Source → Native
    admitted : ∀ x → Member classifier (encode x)
    decode : (x : Native) → Member classifier x → Source
    source-roundtrip : ∀ x → decode (encode x) (admitted x) ≡ x
    native-roundtrip : ∀ x evidence → encode (decode x evidence) ≡ x

module Transport {Source Native Classifier : Set}
  {Member : Classifier → Native → Set}
  (binding : Binding Source Native Classifier Member) where
  open Binding binding

  record Value : Set where
    constructor member
    field
      value : Native
      evidence : Member classifier value

  encodeValue : Source → Value
  encodeValue x = member (encode x) (admitted x)

  decodeValue : Value → Source
  decodeValue (member x evidence) = decode x evidence

  -- Equality of payloads does not assert proof irrelevance for membership.
  payload-roundtrip : ∀ x → Value.value (encodeValue (decodeValue x)) ≡ Value.value x
  payload-roundtrip (member x evidence) = native-roundtrip x evidence

  record Container (Payload : Set) : Set where
    constructor container
    field
      typeArgument : Classifier
      sameParameter : typeArgument ≈ classifier
      contents : Payload

  pack : ∀ {Payload} → Payload → Container Payload
  pack payload = container classifier (same classifier) payload

  parameter-preserves : ∀ {Payload} (c : Container Payload)
    → Container.typeArgument c ≈ classifier
  parameter-preserves = Container.sameParameter

  encodeList : List Source → List Value
  encodeList [] = []
  encodeList (x ∷ xs) = encodeValue x ∷ encodeList xs

  decodeList : List Value → List Source
  decodeList [] = []
  decodeList (x ∷ xs) = decodeValue x ∷ decodeList xs

  list-roundtrip : ∀ xs → decodeList (encodeList xs) ≡ xs
  list-roundtrip [] = refl
  list-roundtrip (x ∷ xs) rewrite source-roundtrip x | list-roundtrip xs = refl

  encodeMaybe : Maybe Source → Maybe Value
  encodeMaybe nothing = nothing
  encodeMaybe (just x) = just (encodeValue x)

  decodeMaybe : Maybe Value → Maybe Source
  decodeMaybe nothing = nothing
  decodeMaybe (just x) = just (decodeValue x)

  maybe-roundtrip : ∀ x → decodeMaybe (encodeMaybe x) ≡ x
  maybe-roundtrip nothing = refl
  maybe-roundtrip (just x) = cong just (source-roundtrip x)

  orElse-preserves : ∀ x fallback →
    encodeMaybe (orElse x fallback) ≡ orElse (encodeMaybe x) (encodeMaybe fallback)
  orElse-preserves nothing fallback = refl
  orElse-preserves (just x) fallback = refl

  append-preserves : ∀ xs ys →
    encodeList (xs ++ ys) ≡ encodeList xs ++ encodeList ys
  append-preserves [] ys = refl
  append-preserves (x ∷ xs) ys = cong (encodeValue x ∷_) (append-preserves xs ys)

  encodeResolution : Resolution Source → Resolution Value
  encodeResolution missing = missing
  encodeResolution (resolved x) = resolved (encodeValue x)
  encodeResolution (ambiguous first second rest) =
    ambiguous (encodeValue first) (encodeValue second) (encodeList rest)

  resolve-preserves : ∀ candidates →
    encodeResolution (resolve candidates) ≡ resolve (encodeList candidates)
  resolve-preserves [] = refl
  resolve-preserves (x ∷ []) = refl
  resolve-preserves (first ∷ second ∷ rest) = refl

  -- All operations preserve the chosen classifier, including empty and
  -- phantom payloads. No finite enumeration of Source is assumed.
  resolve-parameter-preserves : ∀ candidates →
    Container.typeArgument (pack (resolve (encodeList candidates))) ≈ classifier
  resolve-parameter-preserves candidates = same classifier
