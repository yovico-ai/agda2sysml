{-# OPTIONS --safe #-}
module Implication where

open import Agda.Builtin.Bool public using (Bool; true; false)

-- Boolean implication is an indexed relation, with all witnesses retained.
-- It is the logical order between Boolean guards, not an ordered transition
-- table: both constructors remain independently admissible alternatives.
data Implies : Bool → Bool → Set where
  from-false : (conclusion : Bool) → Implies false conclusion
  to-true : (premise : Bool) → Implies premise true

reflexive : (value : Bool) → Implies value value
reflexive false = from-false false
reflexive true = to-true true

transitive : ∀ {a b c} → Implies a b → Implies b c → Implies a c
transitive {c = c} (from-false b) bc = from-false c
transitive (to-true a) (to-true _) = to-true a
