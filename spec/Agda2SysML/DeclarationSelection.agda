{-# OPTIONS --safe #-}
module Agda2SysML.DeclarationSelection where

open import Agda2SysML.Foundation
open import Agda2SysML.Obligations using (Kind)

-- The compiler supplies the classifications of checked declarations. Every
-- project declaration receives at least one requirement; a local annotation
-- is not permission to omit a declaration or to change its semantic role.
data Roles : Set where
  one : Kind → Roles
  more : Kind → Roles → Roles

module Selection (Id Metadata : Set) where
  record Root : Set where
    constructor root
    field
      declaration : Id
      kind : Kind

  data Member {A : Set} (value : A) : List A → Set where
    here : ∀ {rest} → Member value (value ∷ rest)
    there : ∀ {head rest} → Member value rest → Member value (head ∷ rest)

  roots-for : Id → Roles → List Root
  roots-for id (one kind) = root id kind ∷ []
  roots-for id (more kind rest) = root id kind ∷ roots-for id rest

  select : (Id → Roles) → List Id → List Root
  select classify [] = []
  select classify (id ∷ rest) = roots-for id (classify id) ++ select classify rest

  append-left : ∀ {A : Set} {value : A} {left right}
    → Member value left → Member value (left ++ right)
  append-left here = here
  append-left (there member) = there (append-left member)

  append-right : ∀ {A : Set} {value : A} (left : List A) {right}
    → Member value right → Member value (left ++ right)
  append-right [] member = member
  append-right (head ∷ rest) member = there (append-right rest member)

  -- Quantified over the entire supplied project inventory and every assigned
  -- role, including declarations not referenced by a selected state machine.
  no-silent-omissions : ∀ classify {id inventory requirement}
    → Member id inventory → Member requirement (roots-for id (classify id))
    → Member requirement (select classify inventory)
  no-silent-omissions classify here role = append-left role
  no-silent-omissions classify (there {head} member) role =
    append-right (roots-for head (classify head))
      (no-silent-omissions classify member role)

  record Annotated : Set where
    constructor annotated
    field
      requirements : List Root
      annotations : List Metadata

  automatic : (Id → Roles) → List Id → Annotated
  automatic classify inventory = annotated (select classify inventory) []

  add-annotations : List Metadata → Annotated → Annotated
  add-annotations local (annotated required previous) =
    annotated required (previous ++ local)

  annotations-preserve-requirements : ∀ local selected
    → Annotated.requirements (add-annotations local selected)
      ≡ Annotated.requirements selected
  annotations-preserve-requirements local (annotated required previous) = refl
