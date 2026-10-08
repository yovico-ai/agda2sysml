# Formal specification

`DeclarationSelection` governs the default library profile. Every project
declaration receives a nonempty set of roles, selection preserves all inventory
members and roles, and local annotations preserve the default requirements.
Compiler classification and native rendering remain adapter obligations;
documentary source never supplies behavioral evidence.

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

The aggregate command is the formal gate. The Nix check also runs the Haskell
and CLI integration suites and the independent target evaluator. Passing the
formal gate alone does not imply that a SysML emitter has been tested.

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
| [Sharing](Agda2SysML/Sharing.agda) | A reference has a unique value, and expansion reconstructs the original tree | The writer must establish lookup evidence through exact equality and emit an acyclic, complete node table |
| [BooleanLowering](Agda2SysML/BooleanLowering.agda) | Finite Boolean constructor cases preserve their value under every environment substitution, including removal of matched arguments | The adapter must admit exactly this case-tree shape; SysML literal, input and conditional meanings remain rendering obligations |
| [FiniteLowering](Agda2SysML/FiniteLowering.agda) | Exhaustive finite constructor cases preserve every input substitution; native ordered equality tests select the same branch | Concrete enum identities and textual rendering must satisfy the finite carrier correspondence |
| [DependentFamilies](Agda2SysML/DependentFamilies.agda) | Every dependent family is equivalent to the fibres of its own indexed carrier, in both directions and without K | Native domain types and index constraints must implement that carrier and its projection; arbitrary proof erasure is not justified |
| [AlgebraicValues](Agda2SysML/AlgebraicValues.agda) | Typed products and admissible sums preserve fields, payload binding, round trips, distinct constructors, tag preservation, inactive-slot absence, and dispatch | Checked schemas and native field multiplicities must implement the abstract carriers |
| [StructuredIndices](Agda2SysML/StructuredIndices.agda) | Ordered index transport round-trips, preserves and reflects equality, and preserves complete dependent members | Checked constructor payloads, sequence order and repeated positions must survive extraction and rendering |
| [FirstOrder](Agda2SysML/FirstOrder.agda) | Every function in a finite program preserves evaluation under lowering, including ordered nested calls | Bodies can call only preceding definitions; compiler extraction and native invocation must implement the typed expressions, with separate preservation evidence for primitive operations |
| [Specialization](Agda2SysML/Specialization.agda) | Type substitution preserves interpretation for arbitrary families; closed instantiation preserves values in both directions and transports first-order operations | Concrete-use discovery, checked binder interpretation, identity generation, and native lowering must instantiate these laws; open parameters and dependent value indices are outside the rule |

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

`AlgebraicValues` quantifies over arbitrary typed field schemas and field
meanings. It proves record field and complete product preservation, payload
binding expansion, both round trips for a tagged sum constrained to exactly
its selected payload, encoding injectivity, constructor distinction, and
dispatch preservation for arbitrary branch functions. Native field cardinality,
exact-type constraints, and checked compiler telescope order instantiate these
laws; the Agda proof does not parse or execute SysML.

`StructuredIndices` quantifies over arbitrary atom carriers with an invertible
representation. Mapping atoms through an ordered schema preserves every
position and repeated occurrence. Equality reflection prevents distinct schemas
from being merged, and dependent transport preserves the entire member. The
implementation tests execute field encoding, decoding and positional projection
from parsed SysML; they also reject mismatched layouts and member indices.

`FiniteLowering` generalizes exhaustive nullary constructor cases to every finite
domain size. Its lowering law quantifies over arbitrary input substitutions;
`native-select-preserves` justifies ordered equality tests with an exhaustive
last branch. These laws do not admit payload constructors or dependent indices.

`FirstOrder` gives source and native expressions separate typed argument lists
and function tables. Expression and argument preservation compose through calls
and operations with an explicit preservation law. `Program` allows references
only to earlier definitions, excluding recursion and signature-only entries.
`program-preserves` establishes agreement for every function and every argument
tuple. This theorem covers the acyclic subgraph. `RecursiveCalls` supplies the
separate accessibility-induction law for admitted recursive components. Neither
law verifies the Haskell traversal or emitted textual syntax.

`UniverseLevels` proves substitution and closed resolution for arbitrary level
expressions built from parameters, constants, successor, and maximum. Its
runtime model proves environment reconstruction and lookup preservation after
removing resolved static level binders. Compiler extraction, unique inference,
and universe checking must establish this model's premises; these proofs do
not verify the Haskell solver or admit runtime level values.

`IndexedValues` models constructor-specific payloads and result indices for an
arbitrary family. It proves carrier/fibre round trips, preservation of constructor
indices, dependent operations, and dispatch observations. The implementation
admits only finite index domains and supported checked index expressions;
formal quantification over more general families does not expand that compiler
boundary. Native index fields must satisfy the constructor equation, and each
fibre use must satisfy the required index equality.

`DependentRecords` extends the family/fibre correspondence to records whose
members depend on arbitrary preceding field tuples. It proves both round trips,
unchanged prefix values, dependent field preservation, and operation preservation.
The accepted compiler fragment restricts the projected indices to finite domains.

`SpecializedFamilies` composes static interpretation equality with native fibre
encoding inside dependent records. It quantifies over arbitrary static keys,
index domains, preceding field tuples, dependent members, and operations, proving
both round trips, unchanged runtime indices, and operation preservation. Static
substitution/resolution supplies its equality premise; compiler extraction and
substitution are still implementation boundaries.

`DependentSums` extends dependent payload correspondence to arbitrary constructor
tags with their own preceding payload tuples and member families. Its universal
laws preserve both value directions, tags, member indices, dispatch, arbitrary
result-index observations, and operations. They compose with optional-slot and
indexed-family laws; admission of checked telescopes, case substitutions, and
guarded native constraints remains an implementation obligation.


`ComputedIndices` uses the typed acyclic `FirstOrder` program to prove native
index evaluation. Its general expression-substitution theorem justifies helper
argument replacement; comparison requires equality of justified normal forms,
and branch refinement transports a dependent member only along an established
equality. The executable adapter is still responsible for correctly extracting
terms and applying the supported reductions.


`RelationBindings` separates the complete witness telescope from its lexical
variable context. General laws preserve lookup, absolute witness positions,
endpoint evaluation, and endpoint equations in both directions for every
binding/nonbinding layout. This supplies the binding correspondence needed
when the relation adapter instantiates `Relations` from checked constructors.

`Diagnostics` defines the three translation refusal categories. Its general
reason-mapping laws preserve required identities, discharged counts, completeness in both
directions, and strict refusal. Located explanations retain their source and
model links under classification. Assigning the correct category to a checked
compiler boundary remains an executable-adapter obligation.

`SourceOccurrences` separates structural identity from location, ownership, and
shared payloads. General laws preserve catalog identities under relocation,
retain ownership, prevent repacking from merging distinct occurrences, and
require a unique candidate for resolved ownership. Concrete parser recovery
and byte-coordinate conversion remain implementation obligations.

### Derivation and rendering laws

`Agda2SysML.Derivations` models ordered checked/rule origins independently of
semantic values. It proves origin retention under combination and substitution,
rendered-byte preservation under annotation changes, correctness of document
byte measurement, and preservation of interval identity and bounds under shifts.
These general laws do not verify compiler extraction, concrete binder
substitution, specialization, UTF-8 encoding, or the Haskell renderer. Those
adapter obligations are checked by the derivation and public CLI suites. The
model supplies no compiler-extraction evidence.

`SourceAlignment.Direct` defines a relation between resolved first-order source
terms and checked terms under an explicit binder environment. It proves that
renaming checked binders transports alignment, and that selecting an exact
result requires a unique existing alignment proof; ambiguous evidence cannot
be selected. The adapter must establish the relation's premises from compiler
highlighting, pattern origins, and checked terms. These laws do not certify
Agda elaboration, parser recovery, or the Haskell matcher. The signature
transport law additionally proves that arbitrary rebasing preserves resolved
references when every moved index denotes the same telescope slot. Its unused
binder corollary covers insertion of an `Abs` slot in place of `NoAbs`, provided
all prior references are shifted. Concrete signature extraction, metadata
omission, and whole-telescope comparison remain adapter obligations.

The `Derivations.Trace.Readiness` laws quantify over arbitrary checked-source
alignment evidence. Composition retains readiness of both input histories;
adding checked evidence cannot discharge an existing generated boundary.
Fresh nodes obtain their first checked origin at construction. These laws do
not prove Agda extraction or the serialized clause-replay certificates; adapter
and public-contract regressions check those boundaries.

`SourceAlignment.Projection` models the bounded constructor-signature bridge
between a source prefix field application and a checked postfix projection.
For every admitted canonical field, resolved receiver, and runtime environment,
the bridge preserves the projected value. Arbitrary receiver rebasing also
preserves it when moved indices denote the same value. Proper-field registry
validation, exact elimination shape, source catalog paths, and restriction to
constructor signatures remain adapter obligations. No bare receiver occurrence
is claimed where the checked tree stores only a projected term.

`AlgebraicValues.tabulate-inputs` proves that reading every typed input position
reconstructs the entire payload, including separate positions with equal types.
`constructor-helper-preserves` composes that law with constructor encoding for
arbitrary schemas, selected constructors, and payload values. Concrete Agda
telescope extraction (including `Abs`/`NoAbs`), checked-domain provenance paths,
and the existing dependent-family admission conditions remain adapter obligations.
The law does not discharge generated index-contract provenance.

`DependentRecords.Record.InputContract` makes the carrier-index equality
explicit after forgetting a dependent input's fibre evidence. The general laws
prove that the equality is necessary, restores the fibre without changing its
payload, round-trips every admissible input, and refuses any raw input whose
indices cannot agree. These laws quantify over arbitrary prefixes, index
families, and members under `--safe --without-K`. The bounded adapter rule
derives constructor input contracts whose expected index is a resolved earlier
input or one proper field projection of that input; source occurrence paths,
family layout admission, index positions, and `Abs`/`NoAbs` resolution remain
adapter obligations.

`DependentRecords.ProjectedInput` proves that pointwise receiver preservation
preserves every projected index. It transports the input contract in both
directions, restores admissible inputs without changing their payloads, and
refuses projected-index mismatches. The laws quantify over arbitrary prefixes,
record receivers, projections, index families, and members. Canonical field
identity, proper-projection metadata, concrete receiver signatures, and the
single-elimination restriction remain adapter obligations. These laws do not
certify Agda extraction or imply alignment of an invented bare receiver node.


`IndexedValues.Family.ResultContract` states the equality required to treat a
native carrier as a value of an expected result fibre. The general laws prove
that admission preserves the carrier, a constructor's result-index equality
establishes the emitted assertion, the assertion reflects that same equality,
and a mismatching result index refuses admission. They quantify over arbitrary
indices, tags, dependent payloads, and expected results under `--safe --without-K`.
The adapter must separately validate the actual constructor body, terminal type,
canonical finite values, index positions, and binder resolution. A fresh result
assertion does not discharge independent provenance boundaries in result values.


The direct numeric and collection rules are specified in `NaturalValues`,
`SequenceValues`, and `RecursiveCalls`. `DefinitionalReduction` covers the
computational projection and closure laws without proof irrelevance.
`DecisionTree.fallback-preserves` covers nested match fallback, and
`DependencyScope` proves sufficiency of the computational footprint after a
semantics-preserving reduction. `Obligations` distinguishes retained reduction
sources from executable behavior evidence. Adapter admission, termination
certificate use, capture avoidance, and target rendering remain implementation
obligations, exercised by the Haskell and native validation suites.


`RecursiveValues` proves finite constructor-tree/forest correspondence, metadata
preservation and strict decrease along every child edge. `NaturalIndices` proves
finite ordinal bounds and indexed vector length. `CapturedIndices` proves lookup
preservation for both injections into a captured-prefix/runtime environment.
These general laws support the actual `BooleanLowering` core; concrete emitted
results and constraints are verified in the implementation suite.
