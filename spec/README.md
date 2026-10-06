# Formal specification

The Agda core specifies general resolution, validation, transformation, and
coverage laws for agda2sysml. It is part of the
[project specification](../SPECIFICATION.md). All modules use `--safe`, and
the aggregate imports every formal module.

## Checking the specification

The root `flake.nix` and `flake.lock` pin an environment containing Agda 2.8.0,
GHC, and Cabal. The specification depends only on Agda's builtin modules; no
standard library or third-party Agda library is required. With Nix flakes
enabled, run from the repository root:

```text
nix flake check
```

The `spec` check type-checks the aggregate in an isolated build. Only Agda source
and the library descriptor enter that build; local interface caches are excluded.
The flake provides outputs for x86_64 and aarch64 on Linux and macOS. Checks run
on the current host platform by default.

For development, run `nix develop` from the repository root, then enter `spec/`
and run:

```text
agda Agda2SysML.agda
```

For interactive proof development, run `agda --interaction-json` from this same
directory inside the development shell and load the module being edited. The
library descriptor declares this directory as its include path. Generated
interface files are ignored. A separately installed Agda 2.8.0 can also run the
aggregate directly.

The aggregate command is the complete formal gate for this initial repository.
There is no generator implementation, CI workflow, or runtime test suite yet.
Writing or passing a check here does not imply a SysML emitter has been tested.

## Proof coverage

| Module | General law | Boundary |
|---|---|---|
| [Resolution](Agda2SysML/Resolution.agda) | Resolution succeeds exactly for a singleton candidate list; missing resolution requires an empty list | Candidate discovery and canonical deduplication belong to the compiler adapter |
| [Mapping](Agda2SysML/Mapping.agda) | A role is accepted exactly for a unique compatible symbol within the supported profile; acceptance and justified refusal cannot coexist | `Fits` and its decision procedure are supplied by the adapter; YAML and Agda typechecking are not modeled here |
| [DecisionTree](Agda2SysML/DecisionTree.agda) | For every finite decision tree and input, normalized rule selection yields exactly the original outcome | Predicates and effects are total semantic functions; extracting them from compiler terms and rendering them into SysML remain obligations |
| [Relations](Agda2SysML/Relations.agda) | Constructor-style rules and generated semantic edges permit exactly the same source/target pairs | Witnesses and premises are retained abstractly; target edges are not parsed SysML |
| [Coverage](Agda2SysML/Coverage.agda) | A report retains its entire supplied inventory; strict completion accepts fully translated reports and rejects every report containing a textual entry | Inventory discovery, dependency closure, and per-entry translation evidence must be justified separately |
| [Obligations](Agda2SysML/Obligations.agda) | Completion discharges every requirement by its kind; retained proof text cannot discharge executable behavior | The producer must justify its classification and the underlying evidence predicates |
| [Provenance](Agda2SysML/Provenance.agda) | Located transformations preserve origins and compose | Compiler source spans must be correctly supplied |
| [Terms](Agda2SysML/Terms.agda) | Reindexing preserves dependent typing, interpretation, and binder structure at arbitrary universe levels | The local-reference interpretation and compiler lowering need correspondence evidence |

The foundational module supplies small total list, Boolean, equality, and
decision definitions. The laws are universally quantified. There are no
scenario-specific assertions, chosen-state probes, or postulates.

## Semantic domains

`Tree Input Output` describes finite control structure over arbitrary small
input and output sets. Output is the complete observable result; a refused
outcome with a different reason is a different result. Predicates and leaves
are arbitrary total functions, so the proof does not depend on a particular
project's values, commands, or state layout.

`normalization-preserves-evaluation` is proved by induction on the tree. The
supporting lemmas establish list-selection composition and the behavior of
restricting rules by true or false conditions. `normalization-sound` derives
that every selected normalized outcome agrees with evaluation of the tree.
`normalization-preserves-contract` transfers any established property of the
complete original outcome to the selected normalized outcome. No simplification
or reordering of guards is assumed.

The relation model keeps a witness type for each rule, a source expression, a
target expression, and a proposition of premises. Witnesses may include values
and proof evidence. `relation-complete` preserves each permitted source edge;
`relation-sound` rules out invented target edges. The laws preserve alternatives
without imposing executability or uniqueness of results.

`Mapping.Validation` is parameterized by a compatibility relation and a
decision procedure carrying either evidence or a refutation. Its indexed
acceptance/refusal types prevent accepting ambiguous lists or classifying a
compatible singleton as incompatible. This is an abstract validation contract,
not a substitute for specifying the actual dependent signature checks in the
compiler adapter. This validator is invoked only after the adapter establishes
applicability and can decide compatibility. Unsupported signatures must be
reported separately, never supplied as fabricated incompatibility refutations.

`Coverage.Inventory` indexes a report by the complete list of identifiers it
accounts for. Each entry contains translation evidence or an explicit textual
reason. The inventory can represent the inspected corpus or the required
semantic closure; those must remain separately identified in output. Display
roles such as supporting lemma are orthogonal to representation status.

`Evidence : Id → Set` is deliberately a parameter. The completeness gate proves
that evidence is carried, not that an arbitrary producer chose a sufficiently
strong evidence predicate. An implementation correspondence argument must
connect this predicate to the actual source and target semantics. Instantiating
it with a trivial proposition cannot justify a semantic-equivalence claim.

## Remaining correspondence obligations

The first specification leaves the following obligations explicit:

1. Discover every in-scope declaration, canonical identity, and dependency from
   the checked Agda input; preserve origins of generated helper declarations.
2. Implement document parsing, scope resolution, selectors, and role checks in
   accordance with the mapping contract.
3. Lower Agda pattern matching, bindings, dependent refinements, and relevant
   recursive helpers into the semantic domains without losing behavior.
4. Preserve source provenance through normalization and relation translation.
5. Implement target constructs whose SysML interpretation corresponds to the
   semantic rules, including collection order and dependent constraints.
6. Establish that the Haskell implementation follows the formal transformations
   and completeness policy, and that required dependency closure is complete.
7. Validate serialized artifacts, source links, reproducibility, and diagnostic
   behavior using the pinned toolchain.

These are not discharged by the present core proofs. Future formal extensions
must state general laws over their intended domain and stay safely checkable.
Concrete extraction and serialization regressions belong in the implementation
suite when it is introduced.
