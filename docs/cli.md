# Command line and artifact contract

The command forms are:

```text
agda2sysml inspect --library FILE --root MODULE --output DIRECTORY
agda2sysml generate --library FILE --root MODULE --output DIRECTORY
agda2sysml generate --library FILE --root MODULE --output DIRECTORY --diagnostic
agda2sysml inspect --mapping FILE --output DIRECTORY
agda2sysml generate --mapping FILE --output DIRECTORY
agda2sysml generate --mapping FILE --output DIRECTORY --diagnostic
```

`--library` and one or more distinct `--root` options select the default
declaration profile. It requires no YAML and selects every declaration owned
by the input library in the checked import closure. Dependencies enter through
their actual checked references. Names do not decide whether a function is a
proof: a signature ending in Agda's registered equality type can be retained
as an equality contract; other functions keep computational requirements.
Proof-source retention does not erase an additional computational use.
Postulates retain their statement and assumption provenance, while still
requiring structural evidence for a postulated type or behavioral evidence for
a postulated operation. Assumption retention cannot claim executable support.

An optional `--mapping` adds checked local modeling roles in this profile. Its
library and roots must match the command, and its inventory must remain the
import closure. The default required declarations cannot be removed by local
annotations. The mapping-only command preserves the existing selected-model
profile. `--root` without `--library`, duplicate roots, conflicting libraries,
and conflicting annotation roots fail before producing a bundle.

All relative project paths are interpreted relative to the mapping file.
The output directory must not already exist. Input source is never edited.
Commands perform no publication or upload. They operate on the configured local
libraries and pinned validator installation.

`AGDA2SYSML_LIBRARIES_FILE`, when set, names Agda's installed-library registry.
Otherwise Agda uses its normal user registry. The Nix development shell supplies
an empty registry for this project's builtin-only contracts; consuming projects
provide their own dependency registry. The selected `.agda-lib` continues to
govern include paths, dependencies, and checking flags.

`inspect` checks input, resolves mappings, and emits the inventory, diagnostics,
and manifest. It succeeds when checking and mapping validation finish, even when
the inventory identifies translation features requiring additional support.

`generate` is strict unless `--diagnostic` is supplied. Strict generation succeeds
only after every required obligation has evidence and the target validator
accepts the model. Incomplete diagnostic output is never marked complete.
The alpha currently retains an explicitly incomplete bundle in either mode;
omitting `--diagnostic` does not make that bundle complete or change status 2
into success. Check both the exit status and manifest completeness. The
[alpha walkthrough](alpha.md) shows how to handle partial output explicitly.

Exit status is 0 for a completed requested operation, 2 for an incomplete
translation, and 1 for invalid configuration, failed checking, invalid output,
validator failure, or I/O failure. `--help` and `--version` exit successfully.

Artifacts use schema version 1: `inventory.json`, `diagnostics.json`,
`manifest.json`, and, for generation, `correspondence.json` and `model.sysml`.
Generation also writes a self-contained `review.html`: open it locally to
search/filter declarations and inspect checked source, native SysML fragments,
and outstanding requirements. It uses no server, external assets or network.
Each JSON document has `schemaVersion: 1`. Definitions have canonical identities,
kind, module, declared type, source spans, checking assumptions, dependencies,
and representation obligations. Diagnostics have code, severity, message,
affected symbol/model where known, and source or mapping location.

The manifest's `selectionProfile` is `declarations` or `models`. Without YAML,
`mappingDigest` and `mappingVersion` are null. `declarationCatalogue` in the
correspondence report connects every project declaration with a documentary
SysML element, exact source intervals/excerpts, assigned requirements and its
native targets. Documentary packages and retained proof requirements carry no
executable translation evidence. Unsupported bodies still prevent completion.

Translation errors have `code` equal to `unsupported-syntax`,
`unsupported-semantics`, or `unsupported-target-representation`. Each includes
`symbol`, obligation `kind`, affected `models`, and the original `source` link.
The corresponding textual obligation keeps its `reason` and adds `reasonCode`;
discharged obligations have null `reason` and `reasonCode`.

`causes` is an ordered list of failed rule attempts, each with `rule`, `code`,
`message`, and nested `causes`. For calculation fallback, the general algebraic
attempt determines the primary category after the narrower Boolean and finite
rules fail. A helper failure retains its category when caller context is added.
These additive schema-version-1 fields do not alter strict/diagnostic exit status
or coverage accounting. Mapping, compiler, interruption, and resource failures
retain their existing handling.

Repeated checked terms use lossless sharing. A term reference identifies an
immutable entry in the inventory's `nodes` table. References must exist and be
acyclic; recursive Agda definitions remain symbol references, not cycles in the
term table. Reconstructing a shared term must yield the complete original term,
including binder indices and argument metadata. Hash matches alone never prove
node equality: the writer checks equality before reusing an entry. Sharing must
not erase declarations, source spans, proof dependencies, or type information.
References have exactly the shape `{"$node": "ID"}`. A table entry is either
`{"object": {...}}` or `{"array": [...]}`; the contained values are scalars or
references. This encoding also preserves source objects that themselves contain
keys named `$node`, `object`, or `array`. Declaration records retain their
top-level fields for discovery; nested values may be shared.

The manifest records content digests, mapping and toolchain identities, inspected
and required scopes, mode, completion, and validator identity. Source locations
are relative to labeled library roots; absolute local paths are not serialized.
Stable IDs derive from library identity and qualified declaration identity,
never source line numbers or timestamps.

The qualified spelling is accompanied by Agda's checked name identity under the
pinned compiler. This distinguishes anonymous modules, instantiated copies, and
generated declarations that share a printed name. References and declarations
use one checked-identity table; readable names remain separate display metadata.
Original function clauses and expression spans are recovered from the checked
source text with Agda's parser and declaration grouping. A missing source anchor
is explicit and cannot silently justify a native calculation.

The serializer memoizes immutable compiler terms by runtime object identity.
Stable-name hashes select candidate buckets only; equality of stable names is
required for reuse. Every serialized shape still uses content-addressed nodes
with exact equality checks. The pure reference serializer and memoized serializer
share one description, and integration checks compare their reconstructed values.

Failed generation may produce a diagnostic report, but must never leave a
success manifest or a model labeled complete. Artifact publication is staged in
a sibling temporary directory and finalized only after serialization succeeds.
An output directory that appeared after validation must not be overwritten.

Multiple entry modules are combined only when repeated checked source modules,
checking options, resolved roles, and shared node identities agree. Generated
signature support is unioned by checked identity. A conflict is a failed check,
not a last-writer-wins inventory. Roots are merged incrementally to avoid keeping
multiple complete import closures in memory.

The manifest identifies the generator binary by SHA-256, the selected library
descriptor by SHA-256, and the configured dependency requirements. When Git is
available it records the input repository revision and whether the repository
was dirty or its revision/status metadata changed during checking. Source content digests remain authoritative
for the checked text. Git metadata is supplementary, never a substitute for those
digests; no remote URL or absolute repository path is recorded.

The inventory also records normalized project/model presentation: titles,
canonical state/command/transition references, selected binders, outcome
categories, invariants and selected theorems. This metadata is separate from
executable definitions and cannot strengthen their semantics. The configured
library's absolute path is excluded. Correspondence links model roles to emitted
target elements when a native rule is available.

For admitted first-order callers, `correspondence.json` includes
`calculationDependencies`: each entry records the canonical caller `symbol`,
its emitted `target`, and distinct direct `callees` with the same identity/target
fields. Repeated calls share a dependency entry; their argument order and
multiplicity remain in the checked inventory and generated expressions. A native
caller is admitted only after every reachable helper body is supported. Recursive
components additionally require checked termination from safe Agda modules;
unsupported outgoing dependencies invalidate the entire affected call closure.

`specializations` records each concrete declaration's checked source `symbol`,
generated `instance` identity, ordered type `arguments`, and emitted `targets`.
Type arguments retain canonical identities recursively. The checked inventory
contains the original declarations; instance obligations link back to those
declarations through `source.checkedDefinition`. Field targets refer to their
owning native carrier when no standalone projection calculation is required.

`native.concrete-instantiations` discharges a generic dependency only through
its nonempty list of required `instances`, each of which must discharge the
same obligation kind. This is completion for those concrete uses, not a claim
that the generic template is executable for arbitrary type arguments. A generic
declaration selected directly as a mapping role remains incomplete. Coverage
reports count inspected source definitions separately from specialized definitions;
the required-definition and obligation totals include both.

Closed universe-level arguments appear in `specializations[].arguments` as
`{"level": 2}`, interleaved with type arguments in checked telescope order.
Equivalent closed level expressions use the same identity. The
`static.universe-level` rule records compiler level dependencies without a runtime
target; unresolved or ambiguous levels prevent complete generation.

For finite indexed families, `algebraicCarriers[].indices` records each index's
position, native domain and field target. Constructors record `resultIndices`,
and constrained payload/record fields record `refinements`. `indexContracts`
links calculation inputs/results to their emitted native assertion expressions.
These entries report the accepted fragment; arbitrary computed indices still
produce incomplete diagnostics.

For dependent records, payload `refinements` reference earlier field targets,
while projection `indexContracts` reference the actual receiver's fields.
Constructor `indexContracts` retain dependencies between ordered inputs.

For specialized indexed families, instance `arguments` contain only static
type/universe arguments. Runtime index expressions remain in `algebraicCarriers`
and `indexContracts`. When a fixed indexed type is itself a static argument, its
nested `arguments` retain entries with `runtimeType` and `index` (a constructor
identity and ordered static `arguments`, or a retained input/projection form).
This preserves distinct fixed fibres in outer instance identities.

For dependent sum constructors, payload `refinements` reference earlier
constructor-local payload targets. Native `admissibility` guards those
relationships by the constructor tag and enforces active/inactive slot
multiplicities. Constructor `indexContracts` also retain the corresponding
ordered input and result-index relationships.

Computed finite index calls remain explicit in carrier refinements and calculation
contracts. `calculationDependencies` includes calls from input and result indices
as well as bodies. Only helpers admitted by the finite acyclic rule can occur in
these indices; unresolved equality remains an incomplete diagnostic.

### Source occurrence catalog

Each inventory module now includes `sourceCorrespondence.version: 1`. This
catalog describes parsed source syntax; it does not claim expression-to-checked
or expression-to-SysML alignment. Existing `sourceSyntax`, declaration identities,
semantic coverage, and strict-mode behavior remain available unchanged.

`checkedTextDigest` hashes the module's exact checked UTF-8 `sourceText`.
`coordinateSystem` is `utf8-byte-offsets-zero-based-half-open`. Each occurrence
has these fields:

| Field | Meaning |
|---|---|
| `id`, `module`, `path` | The ID is the JSON encoding of `[module, path]`; `path` is an ordered list of child indices. Coordinates, payload hashes, and ownership are excluded. |
| `parent` | Parent occurrence ID, or null for a catalog root. |
| `role` | Parsed syntax role, such as `function`, `clause`, `rhs`, `raw-application`, `identifier`, `constructor-signature`, or `typed-binding`. |
| `anchor`, `binding` | Nearest declaration anchor ID; declaration nodes also retain their binding-name navigation span. |
| `navigation`, `intervals` | Agda line/column navigation and ordered disjoint byte intervals into checked text. Intervals retain gaps rather than using an enclosing envelope. |
| `rangeUnavailable` | Null for valid nonempty intervals; otherwise `source-range-unavailable` or `invalid-source-range`. |
| `syntaxUnavailable` | Explicit reason when declaration grouping or detailed traversal is unavailable. The enclosing syntax occurrence is retained. |
| `owner`, `ownerCandidates`, `ownerUnavailable` | Canonical checked owner when exactly one declaration matches binding module/span; otherwise null owner with missing/ambiguous reason and candidate identities. Children inherit their nearest declaration's result. |

`declarationAnchors` accounts for every checked declaration in the module, with
its `symbol`, directly owned anchor `occurrences`, `unavailable` reason, and an
optional generated-helper `contextOwner`. A helper's parent is navigation context,
not a replacement for its missing source anchor. Ownership is attached after
root merging and does not expand checked expression bodies.

The catalog traverses function clauses and nested with-clauses, explicit local
and module declarations, datatype/record signatures, constructor and field
signatures, typed binders, and common concrete expressions: identifiers, literals,
raw/ordinary applications, parentheses, hidden/instance arguments, function types,
lambdas, lets, dots, equality, and related wrappers. With/rewrite expressions are
retained as syntax. Patterns currently have whole-pattern occurrences; remaining
expression and declaration forms carry explicit traversal limitations. A raw
application is not a resolved function call. Identifier occurrences do not claim
resolved reference targets or checked binder alignment.

Whitespace changes preserve IDs when parsed structure is unchanged. Structural
edits can change descendant paths. Repeated equal expressions remain separate
occurrences even if their checked values share storage. Coordinate conversion
uses Agda's cursor movement and UTF-8 widths, checks position consistency, and
never turns missing ranges into exact zero-length spans. Agda rejects tabs in
source code; the coordinate adapter's tab handling is tested separately.

Finer alignment and target intervals remain planned in the
[source-correspondence draft](source-correspondence.md).

## Checked-to-target derivations

`correspondence.json.sourceCorrespondence.version: 1` contains the additive
checked-to-target trace. It has its own `model.sysml` digest and the same
zero-based, half-open UTF-8 byte coordinates as the source catalog. It does not
change the existing semantic `complete`, coverage, obligations, or diagnostics.

- `checkedRoots` retains the expanded fields actually consumed by native
  lowering, keyed by canonical owner and root (`type`, `compiled`, or projection
  metadata). `templateRoots` retains their original checked inventory fields.
  Prepared roots retain template identity, ordered static arguments, and the
  `native.static-specialization` step. Fine correspondence inside a rebuilt
  specialization is explicitly `specialization-subtree-alignment-unavailable`.
- `checkedOccurrences` identifies uses by owner, root, and mixed field/index
  paths within these roots. Equal shared values have different occurrence paths.
  Each entry carries its value digest and enclosing checked binder/case metadata.
- `targetOccurrences` identifies marked renderer nodes by owner and structural
  document path, with a role, exact rendered interval, derivation reference,
  affected model IDs, and applicable semantic obligations. Equal emitted text
  at different sites remains distinct. Paths are deterministic for the same
  rendering structure; they are not stable IDs across arbitrary renderer edits.
- `derivations` connects each emitted occurrence to ordered checked input
  references. Versioned rule events retain binding environments, branch
  equations, and prior transformation premises. Repeated history events are
  deduplicated; this does not merge output occurrences.
- `rules` lists the rule IDs and versions referenced by this bundle. The rule
  contracts are documented below and in the native translation rule catalog.

Native Boolean, finite, and algebraic case/term events record the checked node
and current binding substitution; algebraic cases also retain index equations.
`native.index-term` records a checked finite-index term. `native.call-site` and
`native.field-access` retain canonical callee/field identities; a call site never
uses the callee body as its origin. `native.finite-choice` and
`native.finite-test` retain the constructor selected by exhaustive case lowering.
`native.boolean-discriminant`, `native.finite-discriminant`, and
`native.algebraic-discriminant` derive the selected input from the checked split
position. `native.case-payload` retains the constructor, payload field and split
position. `native.algebraic-choice` and `native.algebraic-test` record constructor
dispatch, including its generated equality and tag access. Fresh direct nodes
receive their first origin from these checked rules; existing origins and
explicit unavailable boundaries remain premises. A missing checked locator is
`checked-origin-unavailable`; aligned children cannot repair it.
Projection eliminations
and relation endpoints have their own events; relation endpoint premises retain
absolute witness slots separately from the de Bruijn binding stack.
`native.substitution` and `native.normalization` retain the origins of both the
input and replacement. `native.calculation` and `native.relation` refer to the
checked signature. Static specialization records the template and ordered static
arguments; it does not claim unchanged binder positions inside rewritten fields.

Rendering records intervals while producing text. Semantic expression nodes,
constructed field assignments, calculations, and relation endpoint equalities
are marked. Generated structural blocks, unsupported index contracts, existential relation
bodies, and generated expression fragments without finer evidence have explicit
boundaries. Their versioned events (`native.finite-domain`,
`native.algebraic-shape`, `native.index-contract`, `native.relation-existence`,
and `native.generated-expression`) carry an unavailable reason rather than
claiming an expression-level derivation. Enclosing signature evidence remains
useful context. A boundary covers its entire marked subtree.

`checkedPrecision` is `derived` when a marked node has a recorded checked
origin and no direct boundary, or `unavailable` otherwise. This is independent
of source precision. The section reports `sourceAlignment: "partial"` when
some checked occurrences have verified source links, or `"unavailable"` when
none do. Neither value claims source completeness. The source catalog remains
separately available in the inventory.

Broken checked references, duplicate occurrence identities, missing derivations,
stale target digests, and invalid target byte intervals are internal artifact
errors. Generation rejects them before writing an accepted bundle; they do not
become semantic refusals or alter obligation counts. Explicit unavailable
boundaries are valid report entries.

### Direct source alignment

Each inventory module has `sourceAlignment.version: 1`. Its `definitions`
account for source-owned functions with either `links` or an `unavailable`
reason. Rule `source.direct-first-order`, version 1, admits explicit variable
and constructor patterns and prefix RHS calls, constructor applications,
variables, and parentheses. It checks the following evidence:

1. Every character of a source name has consistent compiler highlighting with
   a definition site. Global sites resolve uniquely to canonical compiler
   identities; local references retain their binding site, not their spelling.
2. Source patterns agree with checked constructor identities and hiding.
   Variable patterns agree with `PatOVar` binding sites and de Bruijn indices.
   RHS heads, explicit argument positions, and variable bindings agree with
   the checked clause. The resulting correspondence must be a bijection.
3. Constructor splits are replayed at the compiled tree's actual argument
   positions. The consumed checked patterns establish the leaf's binder
   permutation, and the RHS is checked again in that environment. Every direct
   clause must be accounted for exactly once. Source clause order never selects
   a compiled branch.

Each link contains a `checked` owner/root/path, `source` occurrence ID, source
`clause` ID, `checkedClause` index, resolved `bindings`, and rule/version. The
checked-clause index records the result of verification; it is not a matching
heuristic. A binding's `position` is Agda's one-based character position in the
named module's checked text, used only as binding evidence. Artifact slices
continue to use the catalog's UTF-8 byte intervals.

Compiled `Case` and `Done` occurrences also link to their verified source clauses
under `source.compiled-clause`, version 1. These links are **derived**, never
exact expression identities. Each includes `replay`: the verified `leaf` path,
ordered `splits` (parent path, argument index, canonical constructor, arity,
branch index and child path), and `binderPermutation`. The latter lists original
checked variable indices in leaf-slot order; the corresponding compiled indices
are assigned in reverse slot order. Each replay ends at an independently aligned
RHS with the same clause, checked-clause index, and bindings. A case node retains
links from every verified descendant clause. Unsupported functions receive none.
The adapter validates these certificates against the original compiled tree;
branch ordinals record traversal after canonical matching and do not choose a
source clause. Direct expression links have `replay: null`.

The bounded rule refuses inserted or explicit hidden arguments, dotted/as/
wildcard patterns, operators, literals, lambdas, local definitions, with/rewrite
expansion, overlapping/catchall matching, eta expansion, projection eliminations,
and projection-like function transformations. Missing evidence is
`source-alignment-unavailable`; multiple fully verified candidates are
`source-alignment-ambiguous`. More specific reasons identify syntax, resolution,
and compilation boundaries. Unsupported functions retain no exact links.
In particular, `DependentPayload.copy` is covered, while `observe` requires
hidden argument elaboration and is not covered by this rule.

The target trace's `checkedOccurrences` include `sourceLinks`, `sourcePrecision`
(`exact`, `derived`, or `unavailable`), and `sourceUnavailable`. Referenced
`sourceOccurrences` and their `sourceModules`/checked-text digests are included
in the trace and must agree with the inventory. `exact` requires the verified
direct bridge. Compiled-body preparation may transport it as `derived` under
`source.same-term-structure`, version 1: no static arguments, the same owner and
compiled root, and identical binder/branch/head/argument structure at the same
paths. The comparison allows removal of the textual `modality` field that
preparation omits when rebuilding argument metadata; the original metadata
remains in `templateRoots`. It does not search for equal subterms or transport
through a changed specialization.

### Explicit signature alignment

`sourceAlignment.signatures` reports signature evidence independently of the
body entries in `definitions`. Explicit datatype constructor signatures use the
same bounded rule as function signatures. Record constructor name directives
do not declare full signatures and remain unavailable. Both lists contain an owner, unavailable reason,
and links. A signature is admitted only when its source declaration resolves to
the same canonical owner and the entire explicit first-order telescope matches
its checked type. Named types, explicit prefix applications in indices,
parentheses, arrows, and explicit typed binder groups are supported. Binder
sites come from compiler highlighting. Checked `Abs` extends the environment;
`NoAbs` does not. Each type head, argument, and bound reference must match.
Higher-order domains, hidden/instance insertion, universes, holes, tactics,
nondefault binder modalities, and other elaboration remain unavailable.

Constructor signatures additionally admit explicit `field receiver` expressions
when the receiver is a resolved bound variable and Agda stores exactly one
postfix projection on it. The source field and checked elimination must share
canonical identity. The registry must identify a proper record projection with
principal-argument index 1 and an explicit, default-modality receiver domain.
The whole source application (and surrounding parentheses) links to the actual
checked projected term. There is no invented bare-receiver occurrence inside
that term; the resolved receiver is verified using the signature's binder map.
Nested projections, applied receivers, parameter insertion, and projection-like
functions remain outside this rule. Function signatures and body matching do
not acquire this additional rule.

Signature links use `source.explicit-signature`, version 1, with `checked.root`
set to `type`, a source occurrence, its `signature` catalog anchor, and resolved
`bindings`. Paths cover type wrappers and their terms, never inferred sort
annotations. Precision is `derived`: a source type explains a checked type, but
does not supply all inferred metadata. Agda's standard `Generalized` parser wrapper is
transparent here; any actual added checked binders still fail the full match.
Failure of signature alignment does not
remove independently established body evidence, or conversely.

`source.same-signature-structure`, version 1, transports these links through
zero-static-argument preparation at the same owner and structural path. It
compares every domain and result, canonical type/call/constructor head, argument
position, and explicit default modality. Variable references resolve through
each tree's actual `Abs`/`NoAbs` stack to absolute telescope input positions.
A single postfix projection on a variable additionally retains its canonical
field identity; both the receiver slot and field must agree.
Thus inserting an unused binder requires rebasing references; keeping the same
raw index is not sufficient. The comparison omits inferred sort wrappers,
binder display names, and redundant textual modality metadata; explicit
universe terms are refused. Changed types, captured or free references,
nonempty specialization arguments, and unsupported terms cannot be transported.
Original metadata and indices remain in `templateRoots`; transported link
`bindings` refer to that template, while `bindingContext` describes the prepared
occurrence. The validator recomputes the signature comparison from both roots.

A target's `sourcePrecision` is `derived` only if all its checked inputs have
verified source links and its entire derivation has no unavailable boundary.
Partial evidence cannot promote an enclosing generated subtree. Source
alignment does not affect translation admission, obligations, strict exits, or
SysML bytes. For example, `ComputedIndex.nextPhase` has derived chains for both nested calls
and their input; `invert` and `phaseOf` have derived case-expression chains.
Their enclosing calculations also have derived signature chains.

`native.constructor-tag`, version 1, cites the selected constructor's checked
signature and canonical family. `native.inactive-payload`, version 1, also
cites the inactive slot's constructor signature and records its canonical field
and telescope position. Shape admission has checked both constructors' family
results and ordered telescopes. Source applications additionally retain their
checked occurrence; generated constructor helpers use schema evidence alone.
Supplied payload values retain their existing origins. These annotations leave
the emitted tag, null slots, field order and semantics unchanged.

Missing source alignment for either schema remains a boundary. All four
`DependentPayload.Event` constructor signatures now align, including `embedded`'s
`phase packetValue` projection. Every marked occurrence in `DependentPayload.copy`,
including its four constructions and enclosing calculation, has derived source
evidence. Hidden-parameter `Envelope` signatures remain unavailable. Generated
carrier structure and unsupported index contracts retain explicit boundaries. Complete
source correspondence remains unfinished.

`native.constructor-input`, version 1, derives a generated helper input from
its actual checked telescope domain and the whole constructor signature.
Premises record the constructor, family, payload field, zero-based input
position, and whether that codomain binds. Every declared input is retained,
including a `NoAbs` slot, and equal domain types keep distinct structural paths.
`native.constructor-helper`, version 1, derives the generated construction body
from the same checked schema. Schema extraction checks the constructor kind,
complete telescope arity and result family; missing or inconsistent evidence
remains explicitly unavailable without changing helper generation.

`DependentPayload.Event.quiet` now has derived evidence throughout its helper.
The `marked` and `authorized` helpers also derive throughout, including simple
input index contracts. The `embedded` helper also derives throughout, including
its single-projection input index contract.
Record constructors without full source signatures and specialized signatures
without a source transport rule remain unavailable. Result-index expressions
retain their independent derivation histories.

`native.constructor-input-index`, version 1, derives an entire constructor
input assertion when the expected index is an earlier input. The rule verifies
the constructor's admitted signature, the dependent domain's canonical family,
the admitted family index arity and type, and an explicit checked variable
argument with no eliminations. It resolves that variable through the actual
preceding `Abs`/`NoAbs` stack and requires the same earlier input position as
the emitted refinement. Equal input types never justify swapping positions.
The trace cites the whole constructor signature, dependent input domain,
expected input domain, and actual index-variable occurrence. Premises retain
input/index positions, canonical family/index-field identity, and binder slots.

An admitted assertion has role `index-contract`; unsupported assertions retain
`index-contract-boundary`. Each assertion is checked independently, preserving
its original ordinal and bytes. This is a new derivation for the assertion;
it does not erase generated histories in existing index expressions. Computed,
constant, result-index, and ordinary function contracts remain outside this rule.
Missing source alignment still prevents source-derived precision.

`native.constructor-projected-input-index`, version 1, extends this fresh
assertion derivation to exactly one proper record-field projection of an earlier
input. It requires the checked variable's sole elimination to identify the same
canonical field as the emitted index, resolves its receiver through the actual
`Abs`/`NoAbs` stack, and verifies its record and index carriers against the admitted
record layout. It checks the projection declaration's proper owner, projection
index 1, and explicit relevant unrestricted receiver signature with the matching
record input and finite index result. Equal field types do not justify swapping
field identities or receiver slots. These checked declaration/layout validations
are rule premises; the source origins remain the actual constructor signature,
dependent domain, receiver domain, and whole projected-variable occurrence.
Premises additionally name the canonical `projection` and `record`. No separate
bare receiver node is invented. Nested projections and applied projected values
remain boundaries, as do computed, constant, result-index, and ordinary function
contracts. This rule changes correspondence metadata only.


`native.constructor-result-index`, version 1, derives a constructor result
assertion for a fixed Boolean/finite enum value or a direct constructor input.
It checks the admitted family, result arity and index carrier, the exact selected
constructor body, and the checked terminal family application. The result index
must be an explicit relevant unrestricted argument with no eliminations. A
variable resolves through the complete `Abs`/`NoAbs` telescope to the same input
slot and index carrier. Boolean values use checked builtin identities; enum
values use canonical constructor identities in a validated finite domain.

The origin cites the whole constructor signature, terminal result type, actual
index occurrence, and (for a variable) its input domain. Premises retain the
constructor, family/index field, binder slots, and input position or constant
identity. Result assertions follow all input assertions, preserving ordinals
when adjacent contracts remain unsupported. The supported result assertions of
`Indexed.Permit.waiting`, `Indexed.Permit.granted`, and `Indexed.Flagged.flagged`
now derive. Their existing result-field expression histories remain unchanged;
these three helpers already had derived body evidence and now derive throughout.
Other helpers with unresolved result-value histories remain unavailable.
Projected/computed result indices and ordinary function contracts remain outside
this rule. Generated SysML and semantic admission are unchanged.


## Prepared runtime scope and retained source

`runtimeDependencyClosure` lists the canonical declarations reached from all
selected prepared roots through checked types, bodies, constructors and fields.
`runtimeDependencyClosureVerified` is true only when this nonempty graph is
fully accounted for and admitted. Failure to prepare any selected root disables
reclassification of source dependencies.

A conservative source dependency eliminated by checked preparation can remain
as a discharged `reduction-source` obligation with rule
`source.reduced-dependency`. Its `sourceKind` records the original role and its
`target` is null. `retainedReductionSources` retains the untranslated reason.
These entries are retained source evidence, not native translations of those
helpers. The inventory and assumption report keep their complete source graph.

`preparationEvidence` records demanded term reductions and closure-specialization
arguments/capture types. A closure instance has ordinary runtime inputs and no
runtime closure object; its source link refers to the original checked helper.
`specializations[].arguments` continues to describe type arguments, while closure
arguments are described separately in `preparationEvidence`.
