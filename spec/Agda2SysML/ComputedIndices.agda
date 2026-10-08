{-# OPTIONS --safe #-}
module Agda2SysML.ComputedIndices (Type : Set) (Meaning : Type → Set) where

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; trans; sym; subst)
open import Agda2SysML.AlgebraicValues Type Meaning
  using (Fields; Position; project; encodeFields)
open import Agda2SysML.FirstOrder Type Meaning

-- Internal expansion substitutes actual expressions for a helper's inputs.
-- It is a checking operation; the emitted expression retains native calls.
Substitution : List Signature → List Type → List Type → Set
Substitution fs from to = ∀ {t} → Position t from → Expr fs to t

mutual
  replace : ∀ {fs from to t} → Substitution fs from to
    → Expr fs from t → Expr fs to t
  replace σ (local p) = σ p
  replace σ (literal x) = literal x
  replace σ (call ref args) = call ref (replaceArgs σ args)
  replace σ (apply op args) = apply op (replaceArgs σ args)

  replaceArgs : ∀ {fs from to ts} → Substitution fs from to
    → Args fs from ts → Args fs to ts
  replaceArgs σ none = none
  replaceArgs σ (argument x xs) = argument (replace σ x) (replaceArgs σ xs)

mutual
  replacement-preserves : ∀ {fs from to t} (table : Table fs)
    (σ : Substitution fs from to) (old : Fields from) (new : Fields to)
    → (∀ {u} (p : Position u from) → evaluate table (σ p) new ≡ project p old)
    → (term : Expr fs from t)
    → evaluate table (replace σ term) new ≡ evaluate table term old
  replacement-preserves table σ old new agrees (local p) = agrees p
  replacement-preserves table σ old new agrees (literal x) = refl
  replacement-preserves table σ old new agrees (call ref args) =
    cong (lookup ref table) (replacement-args-preserve table σ old new agrees args)
  replacement-preserves table σ old new agrees (apply op args) =
    cong (Operation.sourceOperation op) (replacement-args-preserve table σ old new agrees args)

  replacement-args-preserve : ∀ {fs from to ts} (table : Table fs)
    (σ : Substitution fs from to) (old : Fields from) (new : Fields to)
    → (∀ {u} (p : Position u from) → evaluate table (σ p) new ≡ project p old)
    → (args : Args fs from ts)
    → evaluateArgs table (replaceArgs σ args) new ≡ evaluateArgs table args old
  replacement-args-preserve table σ old new agrees none = refl
  replacement-args-preserve table σ old new agrees (argument x xs)
    rewrite replacement-preserves table σ old new agrees x
          | replacement-args-preserve table σ old new agrees xs = refl

-- This includes heterogeneous finite input/output domains and arbitrary
-- acyclic helper depth. FirstOrder supplies the admitted program construction.
index-preserves : ∀ {fs context t} (program : Program fs)
  (index : Expr fs context t) (env : Fields context)
  → nativeEvaluate (targetProgram program) (lower index) (encodeFields env)
    ≡ evaluate (sourceProgram program) index env
index-preserves program index env = expression-preserves (program-preserves program) index env

-- Equality after justified expansion permits the same dependent member at
-- either index. No equality is inferred from a helper's signature alone.
comparison-sound : ∀ {fs context t} (table : Table fs)
  (left right normalLeft normalRight : Expr fs context t) (env : Fields context)
  → evaluate table left env ≡ evaluate table normalLeft env
  → evaluate table right env ≡ evaluate table normalRight env
  → normalLeft ≡ normalRight
  → evaluate table left env ≡ evaluate table right env
comparison-sound table left right normalLeft .normalLeft env left-ok right-ok refl =
  trans left-ok (sym right-ok)

-- A selected constructor establishes equality of its computed result index
-- and the scrutinee index. Substitution is permitted only under that equality;
-- this does not invert a possibly non-injective helper.
branch-refinement : ∀ {t} (Member : Meaning t → Set) {left right : Meaning t}
  → left ≡ right → Member left → Member right
branch-refinement Member equation member = subst Member equation member
