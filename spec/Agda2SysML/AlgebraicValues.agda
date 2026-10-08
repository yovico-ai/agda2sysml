{-# OPTIONS --safe #-}
module Agda2SysML.AlgebraicValues (Atom : Set) (Meaning : Atom → Set) where

open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; trans; sym; Empty)

-- A field schema retains position and type. Atomic meanings may themselves
-- be previously justified record or sum carriers; no finite-value assumption.
data Fields : List Atom → Set where
  nil : Fields []
  cons : ∀ {a as} → Meaning a → Fields as → Fields (a ∷ as)

data NativeFields : List Atom → Set where
  empty : NativeFields []
  entry : ∀ {a as} → Meaning a → NativeFields as → NativeFields (a ∷ as)

encodeFields : ∀ {as} → Fields as → NativeFields as
encodeFields nil = empty
encodeFields (cons x xs) = entry x (encodeFields xs)

decodeFields : ∀ {as} → NativeFields as → Fields as
decodeFields empty = nil
decodeFields (entry x xs) = cons x (decodeFields xs)

fields-roundtrip : ∀ {as} (xs : Fields as) → decodeFields (encodeFields xs) ≡ xs
fields-roundtrip nil = refl
fields-roundtrip (cons x xs) rewrite fields-roundtrip xs = refl

native-fields-roundtrip : ∀ {as} (xs : NativeFields as) → encodeFields (decodeFields xs) ≡ xs
native-fields-roundtrip empty = refl
native-fields-roundtrip (entry x xs) rewrite native-fields-roundtrip xs = refl

data Position (a : Atom) : List Atom → Set where
  first : ∀ {as} → Position a (a ∷ as)
  next : ∀ {b as} → Position a as → Position a (b ∷ as)

project : ∀ {a as} → Position a as → Fields as → Meaning a
project first (cons x xs) = x
project (next p) (cons x xs) = project p xs

nativeProject : ∀ {a as} → Position a as → NativeFields as → Meaning a
nativeProject first (entry x xs) = x
nativeProject (next p) (entry x xs) = nativeProject p xs

projection-preserves : ∀ {a as} (p : Position a as) (xs : Fields as)
  → nativeProject p (encodeFields xs) ≡ project p xs
projection-preserves first (cons x xs) = refl
projection-preserves (next p) (cons x xs) = projection-preserves p xs

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

append : ∀ {as bs} → Fields as → Fields bs → Fields (as ++ bs)
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

nativeAppend : ∀ {as bs} → NativeFields as → NativeFields bs → NativeFields (as ++ bs)
nativeAppend empty ys = ys
nativeAppend (entry x xs) ys = entry x (nativeAppend xs ys)

append-preserves : ∀ {as bs} (xs : Fields as) (ys : Fields bs)
  → encodeFields (append xs ys) ≡ nativeAppend (encodeFields xs) (encodeFields ys)
append-preserves nil ys = refl
append-preserves (cons x xs) ys rewrite append-preserves xs ys = refl

-- A constructor split replaces one scrutinee with its ordered payload,
-- between arbitrary prefix and suffix environments.
payload-binding-preserves : ∀ {as bs cs} (prefix : Fields as) (payload : Fields bs) (suffix : Fields cs)
  → encodeFields (append prefix (append payload suffix))
    ≡ nativeAppend (encodeFields prefix) (nativeAppend (encodeFields payload) (encodeFields suffix))
payload-binding-preserves prefix payload suffix
  rewrite append-preserves prefix (append payload suffix) | append-preserves payload suffix = refl

-- A sum is exactly one constructor with its complete, typed payload.
data Sum : List (List Atom) → Set where
  here : ∀ {as rest} → Fields as → Sum (as ∷ rest)
  there : ∀ {as rest} → Sum rest → Sum (as ∷ rest)

data Tag : List (List Atom) → Set where
  selected : ∀ {as rest} → Tag (as ∷ rest)
  later : ∀ {as rest} → Tag rest → Tag (as ∷ rest)

data Slots : List (List Atom) → Set where
  noSlots : Slots []
  slot : ∀ {as rest} → Maybe (NativeFields as) → Slots rest → Slots (as ∷ rest)

absent : (schema : List (List Atom)) → Slots schema
absent [] = noSlots
absent (as ∷ rest) = slot nothing (absent rest)

-- This is the target constraint: the selected constructor has all of its
-- fields, and every other constructor has none. Inactive payload is not data.
data Active : ∀ {schema} → Tag schema → Slots schema → Set where
  at-selected : ∀ {as rest} {xs : NativeFields as}
    → Active selected (slot (just xs) (absent rest))
  at-later : ∀ {as rest} {t : Tag rest} {ss : Slots rest}
    → Active t ss → Active (later {as} t) (slot nothing ss)

record Native (schema : List (List Atom)) : Set where
  constructor tagged
  field
    tag : Tag schema
    slots : Slots schema
    admissible : Active tag slots
open Native

skip : ∀ {as schema} → Native schema → Native (as ∷ schema)
skip (tagged t ss proof) = tagged (later t) (slot nothing ss) (at-later proof)

encode : ∀ {schema} → Sum schema → Native schema
encode (here xs) = tagged selected (slot (just (encodeFields xs)) (absent _)) at-selected
encode (there value) with encode value
... | tagged t ss proof = tagged (later t) (slot nothing ss) (at-later proof)

-- A representation tag denotes the same constructor as the source sum.
sourceTag : ∀ {schema} → Sum schema → Tag schema
sourceTag (here xs) = selected
sourceTag (there value) = later (sourceTag value)

tag-preserves : ∀ {schema} (value : Sum schema)
  → tag (encode value) ≡ sourceTag value
tag-preserves (here xs) = refl
tag-preserves (there value) = cong later (tag-preserves value)

-- Constructor positions, rather than payload type equality, distinguish slots.
-- Different constructors may have identical payload schemas.
schemaAt : ∀ {schema} → Tag schema → List Atom
schemaAt (selected {as}) = as
schemaAt (later t) = schemaAt t

slotAt : ∀ {schema} (position : Tag schema) → Slots schema
  → Maybe (NativeFields (schemaAt position))
slotAt selected (slot xs ss) = xs
slotAt (later position) (slot xs ss) = slotAt position ss

data Different : ∀ {schema} → Tag schema → Tag schema → Set where
  selected-later : ∀ {as rest} {t : Tag rest} → Different (selected {as}) (later t)
  later-selected : ∀ {as rest} {t : Tag rest} → Different (later {as} t) selected
  later-later : ∀ {as rest} {t u : Tag rest} → Different t u → Different (later {as} t) (later u)

absent-at : ∀ {schema} (position : Tag schema)
  → slotAt position (absent schema) ≡ nothing
absent-at selected = refl
absent-at (later position) = absent-at position

inactive-slot-absent : ∀ {schema} {chosen other : Tag schema} {ss : Slots schema}
  → Active chosen ss → Different chosen other → slotAt other ss ≡ nothing
inactive-slot-absent at-selected (selected-later {t = other}) = absent-at other
inactive-slot-absent (at-later proof) later-selected = refl
inactive-slot-absent (at-later proof) (later-later different) = inactive-slot-absent proof different

-- A helper supplies every declared input by its typed position. Equal field
-- types do not merge positions, and an unused binder still occupies a slot.
tabulate : ∀ {as} → (∀ {a} → Position a as → Meaning a) → NativeFields as
tabulate {[]} get = empty
tabulate {a ∷ as} get = entry (get first) (tabulate (λ p → get (next p)))

tabulate-inputs : ∀ {as} (xs : NativeFields as)
  → tabulate (λ p → nativeProject p xs) ≡ xs
tabulate-inputs empty = refl
tabulate-inputs (entry x xs) = cong (entry x) (tabulate-inputs xs)

sourceConstructor : ∀ {schema} (chosen : Tag schema) → Fields (schemaAt chosen) → Sum schema
sourceConstructor selected xs = here xs
sourceConstructor (later chosen) xs = there (sourceConstructor chosen xs)

nativeConstructor : ∀ {schema} (chosen : Tag schema) → NativeFields (schemaAt chosen) → Native schema
nativeConstructor selected xs = tagged selected (slot (just xs) (absent _)) at-selected
nativeConstructor (later chosen) xs = skip (nativeConstructor chosen xs)

constructor-preserves : ∀ {schema} (chosen : Tag schema) (xs : Fields (schemaAt chosen))
  → nativeConstructor chosen (encodeFields xs) ≡ encode (sourceConstructor chosen xs)
constructor-preserves selected xs = refl
constructor-preserves (later chosen) xs = cong skip (constructor-preserves chosen xs)

constructor-helper-preserves : ∀ {schema} (chosen : Tag schema) (xs : Fields (schemaAt chosen))
  → nativeConstructor chosen (tabulate (λ p → nativeProject p (encodeFields xs)))
    ≡ encode (sourceConstructor chosen xs)
constructor-helper-preserves chosen xs =
  trans (cong (nativeConstructor chosen) (tabulate-inputs (encodeFields xs)))
    (constructor-preserves chosen xs)

-- The general admissibility theorem applies to every encoded sum value.
encoding-inactive-absent : ∀ {schema} (value : Sum schema) (other : Tag schema)
  → Different (tag (encode value)) other → slotAt other (slots (encode value)) ≡ nothing
encoding-inactive-absent value other different =
  inactive-slot-absent (admissible (encode value)) different

decode : ∀ {schema} → Native schema → Sum schema
decode (tagged selected (slot (just xs) _) at-selected) = here (decodeFields xs)
decode (tagged (later t) (slot nothing ss) (at-later proof)) = there (decode (tagged t ss proof))

sum-roundtrip : ∀ {schema} (value : Sum schema) → decode (encode value) ≡ value
sum-roundtrip (here xs) rewrite fields-roundtrip xs = refl
sum-roundtrip (there value) = cong there (sum-roundtrip value)

native-roundtrip : ∀ {schema} (value : Native schema) → encode (decode value) ≡ value
native-roundtrip (tagged selected (slot (just xs) _) at-selected)
  rewrite native-fields-roundtrip xs = refl
native-roundtrip (tagged (later t) (slot nothing ss) (at-later proof)) =
  cong skip (native-roundtrip (tagged t ss proof))

encoding-injective : ∀ {schema} {x y : Sum schema} → encode x ≡ encode y → x ≡ y
encoding-injective {x = x} {y = y} equal =
  trans (sym (sum-roundtrip x)) (trans (cong decode equal) (sum-roundtrip y))

constructors-distinct : ∀ {as rest} {xs : Fields as} {other : Sum rest}
  → encode (here xs) ≡ encode (there other) → Empty
constructors-distinct {xs = xs} {other = other} equal
  with encoding-injective {x = here xs} {y = there other} equal
... | ()

-- Constructor selection preserves every payload and branch result, for any
-- result carrier. Branch order is the order of distinct checked constructors.
data Handlers (Result : Set) : List (List Atom) → Set where
  none : Handlers Result []
  branch : ∀ {as rest} → (Fields as → Result) → Handlers Result rest
    → Handlers Result (as ∷ rest)

dispatch : ∀ {schema Result} → Handlers Result schema → Sum schema → Result
dispatch (branch f fs) (here xs) = f xs
dispatch (branch f fs) (there value) = dispatch fs value

nativeDispatch : ∀ {schema Result} → Handlers Result schema → Native schema → Result
nativeDispatch (branch f fs) (tagged selected (slot (just xs) _) at-selected) = f (decodeFields xs)
nativeDispatch (branch f fs) (tagged (later t) (slot nothing ss) (at-later proof)) =
  nativeDispatch fs (tagged t ss proof)

dispatch-preserves : ∀ {schema Result} (fs : Handlers Result schema) (value : Sum schema)
  → nativeDispatch fs (encode value) ≡ dispatch fs value
dispatch-preserves (branch f fs) (here xs) rewrite fields-roundtrip xs = refl
dispatch-preserves (branch f fs) (there value) = dispatch-preserves fs value
