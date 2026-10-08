# Finer source correspondence: draft contract and implementation plan

Status: the source catalog, checked-to-target trace, and bounded direct-source
alignment, direct clause-to-target derivations, and bounded explicit signature
alignment and constructor tag/inactive-slot schema derivations are implemented.
Constructor signatures include the bounded single-projection rule described in
[explicit signature alignment](cli.md#explicit-signature-alignment).
See the [source catalog](cli.md#source-occurrence-catalog) and
[checked-to-target contract](cli.md#checked-to-target-derivations) for the current
schemas and explicit boundaries, including [direct alignment](cli.md#direct-source-alignment).
Direct expression and compiled-clause replay chains now reach emitted calls,
case tests and payload projections. Explicit first-order signature chains can
also complete calculation provenance. Constructor tags and inactive payload values
cite checked constructor signatures and source applications; incomplete signatures
retain unavailable boundaries. `DependentPayload.copy` now has derived evidence
for every marked occurrence after aligning `embedded`'s explicit record projection.
Generated constructor-helper inputs and bodies also cite checked telescope
positions and complete schemas. Constructor input contracts whose index is an
earlier input or one proper field projection of an earlier input also derive.
All `DependentPayload.Event` constructor helpers therefore derive throughout.
Constructor result assertions also derive for fixed finite values and direct
inputs; generated result-value histories remain independent. Nested projections,
computed indices, and ordinary function contracts remain boundaries.
General elaboration alignment and complete derivation coverage
of generated subtrees, and source precision claims below remain proposals. Translation admission, CLI exit status, and mapping
behavior are unchanged.

The objective is to explain which source clauses, constructor signatures, and
expressions justify each generated SysML element and expression. The design is
generic across Agda projects. Project mappings select domain roles; they must
not supply handwritten guesses about compiler clause numbering or source spans.

## Evidence from the current implementation

The following observations were checked against Agda 2.8.0's installed API,
the current adapter, and generated inventories of the public contracts. The
inventories' digests were verified, and their relevant checked source text was
compared with the current contract files.

| Boundary | Observed information | Consequence |
|---|---|---|
| Checked module | `Interface` retains `iSource`, scopes, a signature, and highlighting. Its inspected fields do not include a complete checked expression-to-source trace. | Parse the exact checked text, not a later filesystem copy. A complete provenance bridge is additional adapter work. |
| Source parsing | `Source.sourceSyntax` recovers function groups, clause LHS/RHS spans, nested with-clauses, and explicit local definitions. `Compiler.origins` joins groups to definitions by binding module and binding span. | This establishes declaration-level ownership. It does not establish a correspondence between individual source clauses and compiled branches. |
| Checked clauses | `Encoding.clause` exports `clauseFullRange`. Every inspected clause of `Guarded.step`, `ComputedIndex.nextPhase`, and `DependentPayload.copy` has null start/end positions. | Reading the checked clause range is insufficient. Rechecking without interfaces is not a proposed solution. |
| Compiled bodies | The pinned `CompiledClauses'` constructors are `Case`, `Done`, and `Fail`. They carry branches, binders, and terms, without a general source occurrence identifier. `Internal.Term` has no uniform occurrence range field. | A checked expression path is a useful location in the inventory, but is not by itself a source expression location. |
| Generated helpers | `Guarded.with-48` has `withParent = Guarded.step` and no `sourceSyntax` group. Rewrite helpers also retain parent identities. | A parent link supports navigation; it cannot select an exact with-clause or RHS by itself. |
| Constructor signatures | `Witnessed.Recorded.keep` has a binding span at its constructor name, a checked telescope, and empty `sourceSyntax`. | Extend the source catalog to datatype/record signatures and fields; function clauses alone cannot explain relation endpoint constraints. |
| Sharing | `Sharing` interns identical object/array payloads and reconstructs them through `$node` references. | One shared node can occur in multiple source and checked contexts. Its digest must not serve as an occurrence identity. |
| Rendering | Target expressions are converted directly into `Text`; `Target.sourceLink` describes an entire source definition. | Record target expression positions during rendering, and preserve provenance before expressions are rendered. |

`Range'` can contain several intervals; `Source.location` currently reduces
these to a start/end envelope. The proposed catalog retains the intervals.
Highlighting `Aspects.definitionSite` can supply a definition module and source
position. This is a possible identifier-resolution aid, not an expression trace.
Its availability and correspondence to canonical compiler identities still need
implementation evidence. The implemented direct rule checks it for every use
and refuses missing or ambiguous evidence; it does not assume completeness.

Relevant implementation: [source parsing](../src/Agda2SysML/Source.hs),
[compiler adapter](../src/Agda2SysML/Compiler.hs),
[encoding](../src/Agda2SysML/Encoding.hs),
[sharing](../src/Agda2SysML/Sharing.hs),
[target reporting](../src/Agda2SysML/Target.hs), and
[algebraic rendering](../src/Agda2SysML/AlgebraicTarget.hs).

## Proposed contract

### Separate occurrences from semantic identities

Keep existing declaration, specialization, and generated declaration identities.
Add three occurrence catalogs and a derivation graph:

| Record | Required information |
|---|---|
| Source occurrence | Checked module identity and text digest; canonical owner when established; syntactic role; structural occurrence path; parent occurrence; ordered source intervals, or an explicit unavailable reason. |
| Checked occurrence | Canonical checked definition or specialization instance; semantic root (`type`, `clauses`, `compiled`, or projection metadata); traversal path; checked value/node reference; binding context descriptor. |
| Target occurrence | Generated owner identity; structural target-expression path and role; rendered artifact digest and exact intervals; optional SysML qualified name for a named member. |
| Derivation | Rule identifier and version; ordered input occurrence references; output occurrence references; relevant premises, such as branch constructor, binding substitution, static arguments, or index equality justification. |
| Correspondence | Target occurrence; checked occurrence(s); source occurrence(s); derivation references; precision; affected models and obligation reference; reason when source correspondence is unavailable. |

References must resolve within the bundle, or explicitly name a versioned rule
in the generator's rule catalog. A source file uses the existing library/root/
relative-path identity. Absolute local paths and guessed hosting URLs are not
introduced. Source intervals refer to the checked text retained in the inventory;
target intervals refer to the emitted `model.sysml` bytes.

Use zero-based, half-open UTF-8 byte offsets for authoritative artifact slices.
Retain Agda's line/column positions as navigation metadata. Implement and test
conversion from compiler positions against the checked text, including Unicode,
tabs, newline conventions, and multiple intervals; do not treat `posPos` or
columns as byte offsets without conversion. Null compiler ranges remain absent,
not zero-length exact spans. An enclosing envelope can be displayed separately.

Source occurrence IDs use module identity and structural traversal path,
independently of optional ownership; resolving an owner cannot renumber syntax.
Proposed checked/target IDs additionally use their canonical root/instance.
Keep content digests separate from these IDs. Source positions must not influence
semantic declaration identities or generated SysML bytes. Inserting whitespace
must preserve occurrence IDs when the parsed structure is unchanged. Editing
clauses or expression structure may change descendant occurrence IDs; this is
not a promise of persistent identity across arbitrary edits.

Checked paths identify *uses* of shared nodes. Resolve `$node` references using
the inventory's tagged object/array encoding, and keep the full owner/path even
when the resolved value has been memoized. For example, two identical `read permit`
expressions in different branches remain two occurrences.

### State the precision of each link

| Precision | Permitted claim | Required evidence |
|---|---|---|
| `exact` | The listed source occurrence directly supplies the specified checked/target occurrence under an admitted rule. | Resolved source binding context and a verified source-to-checked alignment, followed by a recorded lowering derivation. A span alone is insufficient. |
| `derived` | The target construct is introduced or transformed by a stated rule from the listed origins. | A derivation with all necessary premises and inputs; every source-bearing input reaches a justified origin. Compiler/rule-generated inputs are explicitly identified. |
| `context` | The source owner or a set of candidate clauses is useful for navigation. | Verified ownership, with the unresolved alignment stated. This does not count as exact or derived correspondence. |
| `unavailable` | A source relationship is not established. | An explicit reason, known checked/target references, and any independently established owner context. |

Precision is a statement about evidence, not a confidence score. Do not promote
`context` to `exact` because there is one candidate, equal printed text, equal
clause counts, matching term hashes, or similar names. Never zip source clauses
with constructor branches: compilation may reorder or transform them.

Multiple source occurrences may jointly justify one target occurrence. One
source occurrence may justify several target occurrences. Generated validity
constraints, constructor tags, optional payload slots, inferred static arguments,
and implicit parameters usually need `derived` links to signatures and rule
premises rather than a fabricated source RHS span.

### Preserve provenance through each transformation

The source-to-checked bridge and checked-to-target lowering are separate edges.
An exact checked-to-target edge must remain useful even when its source bridge
is only `context` or `unavailable`.

For the source bridge, initially admit only explicitly described first-order
syntax with resolved names and binder relationships. Align source clauses to
checked clauses by their verified patterns and contexts, then replay the admitted
case transformations into compiled paths. Match supported RHS forms using the
same canonical names, argument positions, and bindings as the checked form.
Document and validate every admitted elaboration transformation. Structural
similarity or unique matching is not an alternative to these conditions.

With-expansion, rewrite helpers, dotted patterns, eta expansion, omitted arguments,
and implicit insertion require their own bridge rules. Keep them unresolved
until those rules exist. If the pinned API cannot provide necessary evidence,
report that boundary and propose a compiler integration change separately;
this draft neither assumes nor authorizes an Agda fork or dependency upgrade.

During native lowering, annotate intermediate expression *occurrences*, including
branch conditions, leaves, calls, projections, and constructed fields. Preserve
binder substitutions and the distinction between telescope slots and actual
`Abs`/`NoAbs` bindings. Preserve callee identities and keep call-site origin
separate from callee-body origin. A callee's span cannot replace its caller's span.

Specialization retains the generic source owner, ordered static arguments,
instance identity, and the derivation connecting the concrete checked occurrence
to its template. Branch substitution and index normalization retain every source
input needed for their result. If a term is discarded or combined, record that
transformation rather than moving its source span onto an unrelated expression.

Rendering consumes the annotated expression and returns text plus occurrence
intervals in one traversal. Do not recover target positions by searching the
finished string: repeated expressions, escaping, and nested calls make that
ambiguous. Formatting characters need no source origin; every semantic target
node does. A node may have multiple emitted intervals when rendering duplicates
it, with a recorded derivation.

### Reporting and compatibility

Proposed representation: additive, separately versioned `sourceCorrespondence`
sections in inventory/correspondence, retaining the existing schema-version-1
fields and whole-definition `source` links. The source catalog lives in the
inventory; checked/target occurrences and derivations live in correspondence.
Existing readers can continue using their current fields. The nested format
version defines interval units, reference kinds, precision, and rule semantics.

Keep semantic coverage and source-correspondence coverage distinct. Define
source-correspondence completeness over the emitted semantic target occurrences:
every required occurrence has an `exact` or justified `derived` chain, and every
reference and interval validates. Count `context` and `unavailable` explicitly.
An empty emitted target set must not imply successful project translation.
Full project acceptance requires both semantic and source-correspondence coverage,
as required by the project specification.

Implementation recommendation: introduce these reports without silently changing
existing strict-mode exits. A later, explicitly approved compatibility stage
should decide when strict success also requires source-correspondence completeness.
Until then, a passing semantic `complete` flag must not be described as satisfying
the full source-correspondence acceptance criterion. Missing provenance cannot
turn a textual semantic obligation into a discharged one.

Provenance limitations belong in the source-correspondence report, with stable
reasons such as `source-anchor-unavailable`, `source-alignment-unavailable`,
`source-alignment-ambiguous`, and `compiler-generated-origin-unresolved`.
Broken references, invalid intervals, or fabricated precision are malformed
artifacts, not ordinary limitations. Their eventual CLI failure handling must be
specified in the implementation stage; it must not inflate semantic refusal counts.

## Worked checks against public contracts

These are observed cases and proposed outcomes, not claims that the proposed
trace has already been generated. Line numbers identify the reviewed source
snapshot and are not IDs.

| Public contract | Observed current evidence | Required proposed outcome |
|---|---|---|
| [ComputedIndex](../contracts/ComputedIndex.agda), `nextPhase`, line 18 | One recovered RHS span, columns 15–33, contains `phaseOf (invert b)`. The compiled leaf contains a `phaseOf` call whose argument is an `invert` call whose argument is variable 0. | Distinct source and target occurrences for both applications and the variable. Preserve the outer/inner relationship, canonical callee identities, and argument binding. Whole-RHS ownership alone remains `context`. |
| [DependentPayload](../contracts/DependentPayload.agda), `observe`, lines 28–29 | Two different clauses contain `read permit`; all four checked clause ranges are absent. | Keep the two occurrences separate even if their encoded terms share a node. Clause/branch correspondence must establish the different payload bindings. |
| [Guarded](../contracts/Guarded.agda), `step`, lines 23–25 | The second source clause has two nested with-clauses, a null direct RHS span, and a generated checked helper with a parent link but no source group. | Preserve clause nesting. Record parent context now; require a with-expansion derivation before selecting either nested RHS as a helper/branch origin. Do not invent a direct RHS for the with-parent. |
| [Witnessed](../contracts/Witnessed.agda), `Recorded.keep`, line 11 | Constructor-name binding span and checked signature; no function source group. The second witness is a nonbinding argument. | Catalog the constructor signature and argument/index occurrences. Derive generated endpoint equalities from result indices while retaining the unused witness slot. The constructor name span alone is not the endpoint expression span. |
| [RegisterWorkflow](../contracts/RegisterWorkflow.agda), `sequence`, line 10 | Source contains two nested `step` calls. This source was inspected; its generated bundle was not part of this stage's artifact audit. | Use it as an implementation acceptance case for distinct call-site positions with the same callee. Callee declaration links cannot substitute for either call-site link. |

## Formal obligations to add during implementation

The existing [Provenance](../spec/Agda2SysML/Provenance.agda) module proves that
one attached origin survives a value transformation. It does not establish
source alignment, merging of origins, binding substitution, or renderer spans.

Extend the formal model with general laws, quantified over arbitrary occurrence
identities, environments, source sets, and derivations:

1. Every correspondence reference resolves to a well-formed occurrence; a
   claimed exact source origin requires alignment evidence.
2. Derivation composition preserves its necessary origins and cannot promote
   an unresolved source input into exact provenance. Generated premises remain
   explicitly generated.
3. Sharing changes storage identity without merging distinct occurrence paths.
4. Substitution, branch refinement, and specialization preserve the applicable
   origins and binder/instance relationships under their stated premises.
5. Rendering preserves the semantic expression while attaching valid occurrence
   spans; concatenation shifts later spans without changing their identities.
6. Adding or refining provenance leaves semantic evidence and obligation counts
   unchanged, following the separation established by `Diagnostics.Accounting`.

Prove these laws over abstract alignment evidence; do not claim that an abstract
proof verifies Agda extraction. Parser recovery, concrete alignment checks,
coordinate conversion, and SysML renderer correctness remain adapter obligations
with implementation tests. Concrete contract cases belong in those tests, not
in Agda proof modules.

## Implementation sequence and acceptance gates

The first three rows describe the implemented stages. Additional elaboration
rules and acceptance-policy changes require their own approval. The original design
stage contained no generator or formal-model implementation.

| Stage | Work and affected areas | Observable completion and verification |
|---|---|---|
| 1. Source occurrence catalog | Extend `Source` and `Compiler` to catalog function clauses, supported expression syntax, datatype/record signatures, constructors, and fields. Preserve interval sets, checked-text digests, structural paths, parent ownership, and explicit missing anchors. Add the origin/identity formal laws. | Existing source groups remain available. Catalog slices resolve to the checked text; Unicode, tabs, line shifts, repeated expressions, nested with-clauses, and absent ranges are tested. No target-exact claims or semantic admission changes. Run the relevant source regressions and the full Nix gate. |
| 2. Checked-to-target derivations | Add checked occurrence references and derivation records through native lowerers and specialization. Annotate rendering to return target spans and preserve existing model bytes. Extend formal composition/rendering laws. | Every emitted semantic target occurrence has checked/rule origins or an explicit boundary. Repeated calls and shared values retain distinct use paths. Validate all target slices and compare model bytes, declaration identities, and semantic counts. Run target regressions and the full Nix gate. |
| 3. Source-to-checked alignment | Implement a bounded, verified bridge for direct first-order clauses/RHS forms; use resolved source contexts and checked binder transformations. Report unhandled elaboration precisely. | `ComputedIndex.nextPhase` and ordinary finite/payload clauses have validated chains. Reordered branches, identical RHSs, nested binders, hidden arguments, shadowed names, and ambiguous matches cannot produce false exact links. Unsupported with/rewrite paths remain explicit. Run formal, adapter, and public CLI checks through the full Nix gate. |
| 4. Transformed source and acceptance policy | Design and admit additional bridge rules for with/rewrite, eta, dependent patterns, and specialization as justified. Decide strict-mode compatibility and publishable schema policy before changing those interfaces. | General derivation laws and compiler/native evidence cover each newly admitted bridge. Source completeness cannot be claimed for unresolved paths. Review combined acceptance and rerun the full Nix gate after implementation. |

Stage 3's feasibility gate demonstrated that the pinned compiler retains
`Aspects.definitionSite` for local and global uses and `PatOVar` binding sites
in checked patterns, including loaded interfaces. These support the implemented
explicit first-order fragment. Constructor branch replay and a checked binder
permutation establish the compiled paths. `ComputedIndex.nextPhase`, finite
constructor clauses, and `DependentPayload.copy` have verified links. The
repeated `read permit` calls in `DependentPayload.observe` require hidden
argument elaboration and remain unavailable; their checked/target occurrences
remain distinct. No source precision is claimed for that proposed extension.

The continuing feasibility requirement is to demonstrate each extension on the pinned
compiler before expanding its supported fragment. If the interface evidence is
insufficient, keep the result explicitly unresolved and present the concrete
compiler-integration alternative for approval. Source spellings, ordinal joins,
and project-specific mapping overrides are not fallbacks.

Recovery: retain existing artifact fields and comparison bundles throughout
implementation. Any failure of semantic-byte, identity, or obligation-count
preservation blocks completion of that stage. Remove or correct the added trace
rather than changing a translation rule to make its provenance easier.

## Verification of the original draft

The original design stage inspected the installed compiler API and current adapter, checked the
four inventoried contracts above against their checked source snapshots, verified
inventory digests, and reviewed the proposed cases against available and missing
metadata. Local document links and patch whitespace are checked before completion.
That document-only stage changed no generator, test, dependency, or Agda source.
All implementation stages are subject to the full Nix acceptance gate above.
