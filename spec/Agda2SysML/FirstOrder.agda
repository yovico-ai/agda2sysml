{-# OPTIONS --safe #-}
module Agda2SysML.FirstOrder (Type : Set) (Meaning : Type → Set) where

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda2SysML.Foundation using (cong; trans)
open import Agda2SysML.AlgebraicValues Type Meaning
  using (Fields; nil; cons; NativeFields; empty; entry; Position; project;
         nativeProject; encodeFields; projection-preserves)

record Signature : Set where
  constructor signature
  field
    inputs : List Type
    output : Type
open Signature

-- Already justified native operations (cases, construction, projection) can
-- participate in function bodies, but only with their correspondence law.
record Operation (s : Signature) : Set where
  field
    sourceOperation : Fields (inputs s) → Meaning (output s)
    targetOperation : NativeFields (inputs s) → Meaning (output s)
    operation-preserves : ∀ args → targetOperation (encodeFields args) ≡ sourceOperation args
open Operation

-- References are identities with an exact, ordered, first-order signature.
data Ref (s : Signature) : List Signature → Set where
  here : ∀ {fs} → Ref s (s ∷ fs)
  there : ∀ {f fs} → Ref s fs → Ref s (f ∷ fs)

mutual
  data Expr (fs : List Signature) (context : List Type) : Type → Set where
    local : ∀ {t} → Position t context → Expr fs context t
    literal : ∀ {t} → Meaning t → Expr fs context t
    call : ∀ {s} → Ref s fs → Args fs context (inputs s) → Expr fs context (output s)
    apply : ∀ {s} → Operation s → Args fs context (inputs s) → Expr fs context (output s)

  data Args (fs : List Signature) (context : List Type) : List Type → Set where
    none : Args fs context []
    argument : ∀ {t ts} → Expr fs context t → Args fs context ts → Args fs context (t ∷ ts)

mutual
  data NativeExpr (fs : List Signature) (context : List Type) : Type → Set where
    input : ∀ {t} → Position t context → NativeExpr fs context t
    value : ∀ {t} → Meaning t → NativeExpr fs context t
    invoke : ∀ {s} → Ref s fs → NativeArgs fs context (inputs s) → NativeExpr fs context (output s)
    applyNative : ∀ {s} → Operation s → NativeArgs fs context (inputs s) → NativeExpr fs context (output s)

  data NativeArgs (fs : List Signature) (context : List Type) : List Type → Set where
    noArgs : NativeArgs fs context []
    actual : ∀ {t ts} → NativeExpr fs context t → NativeArgs fs context ts → NativeArgs fs context (t ∷ ts)

data Table : List Signature → Set where
  noFunctions : Table []
  function : ∀ {s fs} → (Fields (inputs s) → Meaning (output s)) → Table fs → Table (s ∷ fs)

data NativeTable : List Signature → Set where
  noCalculations : NativeTable []
  calculation : ∀ {s fs} → (NativeFields (inputs s) → Meaning (output s)) → NativeTable fs → NativeTable (s ∷ fs)

lookup : ∀ {s fs} → Ref s fs → Table fs → Fields (inputs s) → Meaning (output s)
lookup here (function f rest) = f
lookup (there ref) (function f rest) = lookup ref rest

nativeLookup : ∀ {s fs} → Ref s fs → NativeTable fs → NativeFields (inputs s) → Meaning (output s)
nativeLookup here (calculation f rest) = f
nativeLookup (there ref) (calculation f rest) = nativeLookup ref rest

mutual
  evaluate : ∀ {fs context t} → Table fs → Expr fs context t → Fields context → Meaning t
  evaluate table (local p) env = project p env
  evaluate table (literal x) env = x
  evaluate table (call ref args) env = lookup ref table (evaluateArgs table args env)
  evaluate table (apply op args) env = sourceOperation op (evaluateArgs table args env)

  evaluateArgs : ∀ {fs context ts} → Table fs → Args fs context ts → Fields context → Fields ts
  evaluateArgs table none env = nil
  evaluateArgs table (argument x xs) env = cons (evaluate table x env) (evaluateArgs table xs env)

mutual
  nativeEvaluate : ∀ {fs context t} → NativeTable fs → NativeExpr fs context t → NativeFields context → Meaning t
  nativeEvaluate table (input p) env = nativeProject p env
  nativeEvaluate table (value x) env = x
  nativeEvaluate table (invoke ref args) env = nativeLookup ref table (nativeEvaluateArgs table args env)
  nativeEvaluate table (applyNative op args) env = targetOperation op (nativeEvaluateArgs table args env)

  nativeEvaluateArgs : ∀ {fs context ts} → NativeTable fs → NativeArgs fs context ts → NativeFields context → NativeFields ts
  nativeEvaluateArgs table noArgs env = empty
  nativeEvaluateArgs table (actual x xs) env = entry (nativeEvaluate table x env) (nativeEvaluateArgs table xs env)

mutual
  lower : ∀ {fs context t} → Expr fs context t → NativeExpr fs context t
  lower (local p) = input p
  lower (literal x) = value x
  lower (call ref args) = invoke ref (lowerArgs args)
  lower (apply op args) = applyNative op (lowerArgs args)

  lowerArgs : ∀ {fs context ts} → Args fs context ts → NativeArgs fs context ts
  lowerArgs none = noArgs
  lowerArgs (argument x xs) = actual (lower x) (lowerArgs xs)

Compatible : ∀ {fs} → Table fs → NativeTable fs → Set
Compatible source target = ∀ {s} (ref : Ref s _) (args : Fields (inputs s))
  → nativeLookup ref target (encodeFields args) ≡ lookup ref source args

mutual
  expression-preserves : ∀ {fs context t} {source : Table fs} {target : NativeTable fs}
    → Compatible source target → (term : Expr fs context t) → (env : Fields context)
    → nativeEvaluate target (lower term) (encodeFields env) ≡ evaluate source term env
  expression-preserves compatible (local p) env = projection-preserves p env
  expression-preserves compatible (literal x) env = refl
  expression-preserves {source = source} {target = target} compatible (call ref args) env =
    trans (cong (nativeLookup ref target) (arguments-preserve compatible args env))
      (compatible ref (evaluateArgs source args env))
  expression-preserves {source = source} compatible (apply op args) env =
    trans (cong (targetOperation op) (arguments-preserve compatible args env))
      (operation-preserves op (evaluateArgs source args env))

  arguments-preserve : ∀ {fs context ts} {source : Table fs} {target : NativeTable fs}
    → Compatible source target → (args : Args fs context ts) → (env : Fields context)
    → nativeEvaluateArgs target (lowerArgs args) (encodeFields env) ≡ encodeFields (evaluateArgs source args env)
  arguments-preserve compatible none env = refl
  arguments-preserve compatible (argument x xs) env
    rewrite expression-preserves compatible x env | arguments-preserve compatible xs env = refl

-- A program can call only functions in its preceding table. This syntactic
-- construction excludes self/mutual recursion and signature-only declarations.
data Program : List Signature → Set where
  emptyProgram : Program []
  define : ∀ {fs} (s : Signature) → Expr fs (inputs s) (output s)
    → Program fs → Program (s ∷ fs)

sourceProgram : ∀ {fs} → Program fs → Table fs
sourceProgram emptyProgram = noFunctions
sourceProgram (define s body rest) = function (evaluate (sourceProgram rest) body) (sourceProgram rest)

targetProgram : ∀ {fs} → Program fs → NativeTable fs
targetProgram emptyProgram = noCalculations
targetProgram (define s body rest) = calculation (nativeEvaluate (targetProgram rest) (lower body)) (targetProgram rest)

program-preserves : ∀ {fs} (program : Program fs) → Compatible (sourceProgram program) (targetProgram program)
program-preserves emptyProgram () args
program-preserves (define s body rest) here args = expression-preserves (program-preserves rest) body args
program-preserves (define s body rest) (there ref) args = program-preserves rest ref args
