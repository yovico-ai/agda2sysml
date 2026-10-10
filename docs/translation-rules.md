# Direct target translation rules

The target contains domain declarations, calculations, and constraints. It has
no Agda syntax objects or evaluator. Every rule has a checked applicability
boundary. A declaration outside these boundaries remains visible with an
undischarged requirement; this catalogue does not narrow the project's eventual
acceptance criteria.

## Boolean values and finite constructor cases

`native.boolean` maps Agda's registered builtin Boolean type and its two
registered constructors to `ScalarValues::Boolean`, `true`, and `false`.
Compiler builtin identities determine applicability, not spelling conventions.
The correspondence is the bijection between the two Boolean carriers.

`native.boolean-cases` translates a checked function whose entire telescope
and result are Boolean. Its compiled body may contain finite Boolean constructor
cases and leaves that are Boolean literals or bound variables. Every split has
both nullary constructors and no additional branches, catch-all, copattern,
eta branch, or lazy match. Each input retains its telescope position. Case
matching removes the selected argument; a leaf's de Bruijn index addresses the
reversed remaining environment. Bound variables are never replaced by their
printed binder names.

The target is a calculation with Boolean input parameters, a Boolean result,
and nested native `if test ? yes else no` expressions. The general
`BooleanLowering.lower-preserves` theorem proves preservation for all trees,
all input environments, and all environment substitutions. The compiler
adapter must establish that the admitted compiled cases have that shape;
the Haskell lowering must implement the same environment removal and lookup.
The rendering obligation maps literals, input references and conditionals to
their SysML Boolean meanings. Validator acceptance checks syntax and typing;
it does not prove that obligation.

Calls, recursion, literal patterns, payload constructors, higher-order inputs,
dependent input types, primitive operations, and incomplete case trees require
other rules. This rule cannot discharge any of them by retaining text or an
opaque helper call.

## Exact textual requirements

`source.statement` retains the checked signature and complete source document.
`source.proof` retains the checked clauses, their referenced declarations, and
complete source document. These discharge statement-retention and proof-source
requirements only. They provide no executable behavior evidence. Checking
assumptions remain attached to the source modules; safe mode on one declaration
does not remove assumptions in its dependency closure.

Statement dependencies retain the statement role, including the definitions of
types appearing only in theorem signatures. If the same declaration is also
required by a transition, its additional executable or structural requirement
must be discharged independently. Record structure includes its constructor
and every declared field.

## Native equality statements

`native.equality-statement` emits a SysML `constraint def` for a checked
function signature ending in Agda's registered equality type. Recognition uses
the builtin's resolved identity, never the theorem's spelling or project.
The constraint retains the supported telescope as typed inputs and compares
the two checked conclusion expressions. It does not execute the proof body
or replace the conclusion with `true`.

Preparation uses the existing type, family, specialization and calculation
rules. Every calculation referenced by the conclusion or input indices must
be admitted. Open type/family bindings and index contracts remain explicit.
Proof-valued hypotheses remain full indexed evidence inputs, with their
constructor payloads and validity constraints. They are not erased or replaced
by Boolean flags. Ordered list conclusions compare their ordered, nonunique
contents rather than their extent-binding metadata.

The proof-source obligation remains `source.proof`, with source and dependency
provenance. Native statement coverage is distinct from calculation coverage:
emitting a constraint does not translate a proof implementation or prove the
constraint in SysML. Unsupported statement preparation or dependencies keep
the exact textual statement and report the reason. An unsuccessful optional
statement attempt does not introduce new required runtime obligations.

`correspondence.json.nativeStatements` lists the checked symbol, equality kind,
`translated` or `textual` status, native target when available, refusal reason
and code otherwise, and proof-source link. The coverage fields
`nativeEqualityStatements` and `textualEqualityStatements` count these attempts
separately. Generated Agda helper declarations can be among them; an authored
law count must identify those separately.

Record equality uses SysML data-value equality, retaining every declared field.
The parsed-model oracle respects field ordering/uniqueness, while the pinned
Pilot has a reproduced limitation comparing equivalent constructed records. See the
[interactive execution limits](interactive-sysml.md#execution-limits).

## Dependent families and abstract parameters

The governing `DependentFamilies` law is universe-polymorphic: a member of a
family at an index corresponds exactly to an element of that family's indexed
carrier constrained to the same index. The carrier is specific to the domain
family. Both round trips are proved without assuming uniqueness of identity
proofs. Implementing this representation in native declarations remains a
lowering obligation; the theorem is not permission to erase arbitrary evidence.

Abstract function parameters also require more than an unbound calculation
result. KerML functions can have side effects and need not behave as pure
mathematical functions. Native totality and functional-consistency constraints
over their type extents are part of the target design; syntax acceptance alone
does not establish purity or a correspondence argument. See
[KerML 1.0, sections 7.4.8 and 7.4.9](https://www.omg.org/spec/KerML/1.0/PDF).

## Finite domain enumerations

`native.finite-domain` maps a closed datatype with no parameters, indices, or
constructor payloads to its own SysML enumeration. Every checked constructor
maps to exactly one distinct enum value. Empty datatypes, abstract datatypes,
and payload constructors are outside this rule.

`native.finite-cases` handles functions whose inputs and result belong to the
same admitted domain. Exhaustive nullary constructor splits remove their
scrutinized argument; leaves retain literals or bound variables. The target
uses constructor equality and nested conditionals, with the last branch
justified by exhaustive coverage. Constructor names are resolved identities,
not matching strings. `FiniteLowering.lower-preserves` proves the general
case-tree translation for every finite domain size, every tree, and arbitrary
input substitutions. `FiniteLowering.native-select-preserves` establishes selection by ordered
constructor-equality tests with an exhaustive final branch. The rendering
obligation identifies native enum equality with distinct constructor identity;
validator acceptance alone does not prove that correspondence.

The native enumeration carrier is closed to its declared values by SysML's
enumeration semantics, including when used as an ordinary attribute type. See
[SysML 2.0, section 7.8.1](https://www.omg.org/spec/SysML/2.0/Language/PDF).

## Relations over finite domains

`native.finite-relation` represents a closed indexed datatype whose indices and
constructor witnesses are Boolean or admitted finite domain values. Each
constructor becomes a named constraint with all its witness parameters and all
endpoint equations. The relation constraint existentially quantifies witnesses
and disjoins the constructor constraints. Constructor order introduces no
priority. Empty constructor sets denote false. Parameters, recursive premises,
and other proposition witnesses require additional rules.

Witness positions follow the full constructor telescope, including unused
arguments. Endpoint variables follow a separate lexical environment: `Abs`
extends it and `NoAbs` leaves it unchanged. Each lexical entry records its
original witness position. Missing binding metadata and out-of-context endpoint
variables are refused; matching witness types cannot justify guessing a slot.
`RelationBindings.lookup-preserves` and `endpoint-preserves` establish this
translation for every binding layout and typed witness environment. Its
`equation-sound` and `equation-complete` laws preserve endpoint equations in
both directions. The `Witnessed` contract and implementation/native tests check
compiler extraction and the executable adapter, including same-type witnesses.

This instantiates `Relations.relation-sound` and `relation-complete` with the
exact checked constructor telescope as the witness domain and the checked
result indices as endpoint expressions. Native quantification ranges over the
whole corresponding finite carrier. The rendering obligation uses KerML type
extents and `ControlFunctions::exists`; the Pilot validates these expressions
but currently does not evaluate every type-extent quantifier. Validation and
executable evaluation are reported separately.

## Records and constructor payloads

`native.algebraic-value` admits concrete closed records and nonempty datatypes
whose complete constructor telescopes use already admitted carriers. These
include Boolean, finite enumerations, and acyclic nests of records and payload
datatypes. Static parameters are handled by specialization; finite dependent
indices have the additional rule below. Unsupported dependent fields, erased or
irrelevant fields and coinductive records are refused. Acyclic admission proceeds
in dependency order; safe inductive recursive families use the checked rule below.

A record becomes an immutable `attribute def` with one singleton attribute for
each checked field. A payload datatype becomes its own attribute definition,
a closed constructor-tag enumeration, and optional attributes for every
constructor payload position. A native constraint requires exactly one value
in every selected constructor field and zero values in all other constructor
fields. Nullary constructors retain their distinct tags. An exact-type
constraint excludes subclass values from the represented closed carrier.
No ownership relationship or occurrence identity is introduced.

Constructor calculations use native `new` expressions with named bindings for
every field. Generated payload names retain constructor identity and position;
declared record fields retain their names. `correspondence.json` includes an
`algebraicCarriers` section connecting each source constructor/payload position
to its native field, constructor calculation, and admissibility constraint.

`native.algebraic-cases` supports heterogeneous input/result carriers,
construction, proper record projections, and exhaustive constructor splits.
Each split replaces its scrutinized binding with all payload fields in checked
order, preserving the preceding and following bindings. Record eta splits
must match the checked record constructor and field order. Leaves check binder
counts, de Bruijn lookup, expression carriers, and every elimination. The
extensions below add fieldwise record definitions, nested fallback matching,
checked recursion, and compile-time closure specialization. Literal patterns
and unresolved higher-order values remain unsupported.

`AlgebraicValues` proves both product and sum round trips, field-projection
preservation, payload-environment expansion, injectivity and constructor
distinction, and dispatch preservation for arbitrary schemas, field meanings,
payloads and result carriers. A target sum is admissible only with its selected
complete product and all other slots absent. Grouping singleton field usages
into that product is the renderer correspondence obligation. Nested carrier
correspondence composes in the admission order.

Native feature access, named construction, classification and null values use
[KerML 1.0, sections 7.4.9.2–7.4.9.4](https://www.omg.org/spec/KerML/1.0/PDF).
The pinned Pilot validates these declarations and evaluates projections,
payload dispatch, and the admissibility predicate on constructed literal inputs.
Its constructor evaluator returns the constructor result feature without
capturing the surrounding invocation context. Consequently it does not reliably
evaluate functions returning newly constructed records whose fields depend on
their inputs. The independent algebraic expression tests cover those lowering
operations; they are not a claim that the Pilot executes them correctly, or an
end-to-end proof of the emitter.

## Ordered schemas as dependent indices

Checked constructor values can appear in a dependent index with their ordered,
typed payloads. Static parameters come from the constructor's expected result
and payload telescope; each payload is checked in the preceding payload context.
Unresolved parameters, wrong domains and wrong payload arities remain refusals.

List schemas use the native ordered, nonunique sequence carrier. Empty and cons
indices retain every atom, including repeated atoms at distinct positions.
Schema construction in validity and calculation constraints carries the same
type-parameter binding as the corresponding value. Schema equality compares
the ordered contents; it does not compare extent bindings as list elements.
Existing membership constraints require the same extent and permit reordered bindings.
Constructor matching can
refine a schema's head and tail and justify a later lazy match only when its
constructor is uniquely determined. This does not infer injectivity for
arbitrary calculation calls.

The generator translates its own `AlgebraicValues.Fields`, `NativeFields` and
`Position`, together with `encodeFields`, `decodeFields`, `project` and
`nativeProject`. Members of a parameterized meaning family retain their complete
payloads and atom indices. `StructuredIndices` proves schema equality reflection
and complete-member transport for arbitrary atom carriers. Parsed SysML tests
compare complete field results and positional projections and reject mismatched
schemas and members. These tests complement the formal laws and target validator;
they are not an end-to-end proof of the Haskell compiler.

Computed schema concatenation also supports `append` and `nativeAppend` through
the structural calculation rule below. Higher-order handlers and other
unsupported definitions in `AlgebraicValues` remain explicit refusals.

The existing `AlgebraicValues.encode` and `decode` also translate. Their native
tagged sum retains the chosen constructor, every typed payload, inactive slots,
and the complete `Active` evidence linking the tag to the slots. Constructor
positions distinguish alternatives even when their payload schemas are equal.
Parsed-model checks compare independently assembled complete results and reject
inconsistent tags, schemas, slots, missing evidence and members at a wrong atom.

Relevant datatype value parameters omitted from constructor terms are recovered
from the expected family. Indexed records store these parameters explicitly;
their projections read the actual receiver's stored parameters. Constructor and
call substitution preserve the separate scopes of caller indices and local
telescope indices. Splitting a value remaps dependent types to the reconstructed
constructor and its ordered payload, rather than reusing stale input positions.
Later family indices and call arguments are checked against actual preceding
values. Unknown arguments do not establish index equality.

Branch facts retain ordinary list reconstruction and the tag of an indexed sum.
Empty-fibre checks may compare payloads only for records or a sum constructor
whose tag is established on both sides. Disjoint nested tags can justify an
impossible branch; an unknown payload or unrelated scrutinee cannot. Recursive
payload comparison stops at a repeated carrier and remains conservative.

## First-order helper calls

### Unused higher-order module parameters

The checked inventory records each declaration's module-parameter count. Before
specialization, a conservative dependency analysis identifies function-valued
module parameters unused by the declaration's retained types, calculations and
matches. Forwarding into another unused parameter is allowed only after the
callee and its dependencies pass the same analysis. Carrier parameters also
require every constructor to leave the parameter unused. Unknown or partial
applications, missing metadata, opaque bodies and unsupported case trees prevent
omission. Stored function payloads use the callable-member rule below;
live callbacks use the callback-input rule rather than being omitted.

An admitted unused parameter occupies a static bookkeeping slot during
specialization and contributes no runtime SysML input. The original quantified
source signature stays in the inventory: the generated behavior is independent
of the choice of any well-typed source function argument. Type parameters,
payloads, dependent indices and evidence retain their existing checks.

Agda module instantiation can create carrier aliases and function aliases.
Carrier identity follows the compiler's recorded alias clause, requiring a
transparent module copy with an ordinary variable telescope. Checked function
aliases can retain their source identity through a supported call to the original
calculation, even though they have no separate handwritten definition. Missing
equations, unsupported callees and unanchored ordinary functions remain refused.

These rules translate the existing `Diagnostics.Accounting.before-count`,
`after-count`, `Before.sources` and `After.sources` operations without changing
their Agda definitions. Parsed-model tests check mixed translated/textual reports,
repeated and reordered identities, empty reports, open evidence families and
unbounded natural identities. Mismatched source lists, reasons and evidence must
fail the emitted contracts.

### Dependent pairs and projected record adapters

Checked, transparent type aliases returning a universe may reduce at known
arguments. One-domain first-order type-family lambdas retain their bound index
separately from runtime telescope positions. Specialization applies those
families to actual preceding fields, retains their complete members and checks
their declared domains and universes. Lambda binder renaming does not change
the native instance identity.

Finite nesting of a nonrecursive generic record, including Agda's dependent
pair type, is admitted independently of polymorphic recursion. A record whose
type captures an earlier runtime index stores that capture explicitly. Its
constructor, projections and validity constraints retain the relationship
between the stored capture, dependent fields and family indices. Construction
does not discard equality evidence.

`DependentRecords.KnownProjection` binds the existing general record adapter
to a checked prefix projection at universe level zero. Its `encode`, `decode`,
`forgetInput` and `admitInput` operations translate to native calculations.
The general round-trip and mismatch-refusal laws remain Agda proofs; parsed
SysML checks compare complete prefixes, members and equality evidence and
reject wrong indices, captures and admission proofs.

Unknown runtime index functions and unsupported family
lambda domains remain explicit refusal boundaries. Alias reduction uses the
existing checked reduction budget; carrier specialization is bounded to 128
active frames. No exhausted budget establishes semantic equivalence.

`native.first-order-calls` admits functions over the existing Boolean,
finite-enumeration, record, and payload carriers. Every input and result has a
concrete admitted carrier. Relevant implicit arguments retain their checked
telescope positions. Erased, irrelevant, unsupported dependent, and higher-order signatures
remain unsupported.

A definition application resolves by canonical compiler identity, checks every
argument against the ordered signature, and emits a positional native calculation
invocation. Zero-argument calls, nested calls, calls inside construction and case
branches, and proper projections from returned records are supported. Partial
applications, extra applications, and projections from the wrong carrier are
rejected. Identical display names do not merge distinct callees.

A signature alone cannot justify a call. The complete reachable call graph must
have supported bodies. Cyclic components additionally require the checked
termination evidence described below. Missing helpers and unsupported bodies
make their callers incomplete, including callers in an otherwise admitted cycle. The correspondence
report records canonical caller/callee identities and emitted target names in
`calculationDependencies`.

`FirstOrder.expression-preserves` and `arguments-preserve` quantify over typed
environments, signatures and ordered argument lists. `program-preserves` proves
that lowering a finite program preserves every callable function, where each
body may refer only to earlier definitions. Primitive operations in those bodies
must carry their own universal preservation law. This composes existing carrier
and case laws; it does not prove the Haskell dependency traversal or parse SysML.

Native positional invocation follows KerML 1.0 section 7.4.9.4, linked above.
The Pilot evaluates nested calls and returned-value projections. The returned
construction limitation described above still applies; an independent test-only
expression evaluator covers calls composed with construction. No evaluator or
generic Agda representation is emitted into the model.

## Concrete type-parameter specialization

Required closed applications of nonrecursive record and datatype families are
represented by distinct native carriers keyed by the checked family identity
and its ordered concrete type arguments. Repeated keys share one declaration;
different arguments remain distinct even for phantom parameters. Constructors,
fields, and first-order operations retain their source identity and an explicit
instantiation correspondence. The checked inventory remains unchanged.

Specialization substitutes type parameters before admitting field and operation
signatures. Every concrete value carrier and operation body must still pass the
existing native rules. All reachable concrete instantiations must be accounted
for; retaining a generic template is insufficient to discharge a concrete use.
Unbound parameters, unsupported dependencies, changing recursive type
instantiations, unresolved higher-order values, and unsupported type-level
expressions remain explicit boundaries.
Leading type and static universe-level parameters are supported as described
below. Value parameters require a separate representation rule.

### Open first-order type parameters

In the automatic declaration profile, a leading type parameter at a fixed
universe is retained as a native **type extent**, an unordered unique
`Base::Anything [0..*]` input named `typeArgumentN`. This is the chosen source
carrier's complete native value set, not a finite sample or a type-name string.
A model can bind it to `all DomainType`; empty and infinite extents are allowed.
Payloads remain direct native domain values. `SequenceFunctions::includes`
constrains a parameter-typed value to its extent. Parameterized records, sums
and list wrappers carry the same extent; `includesOnly` establishes equality of
extents independently of order. Ordered list contents remain finite and
nonunique, separately from the unrestricted extent.

The adapter substitutes distinct symbolic parameter slots into the checked
signature and case tree, then applies the existing native first-order gates.
Calls and constructions pass the corresponding extents. Static checking keeps
parameter positions and family identities distinct; a function cannot inspect
an unknown parameter's constructors. An open root is discharged only by its
own admitted schema, never by unrelated concrete instances. Trace preparation
records distinguish `native.open-parameter-schema` from closed specialization.

`OpenParameters` states the carrier correspondence, both payload transport
directions, parameter consistency, and preservation of resolution, fallback
selection and list concatenation for arbitrary source/native carriers. Its
binding laws are prerequisites, not a proof that every Agda type has a native
representation. CI uses the actual self algorithms, independently parses their
emitted bodies and assertions, checks complete structured results, and rejects
inconsistent extents. This oracle is test code, not an emitted interpreter.

Native validation and independent parsed-target evaluation remain separate
from Pilot execution. In particular, `all DomainType` is not model-level
evaluable in Pilot; it denotes an extent in the target model. Unsupported
higher-order source parameters and dependent signatures
remain explicit boundaries. Directly calling `BaseFunctions::'istype'` with
runtime type metadata is not a dynamic membership test and is not used.

### Indexed family parameters and evidence

An open first-order family parameter such as `Behavioral : Id → Set` is
represented by an unrestricted native membership relation. Its rows retain
every index and a complete native payload. A family member has a domain-specific
native carrier containing the indices, payload and its binding; an existential
constraint requires a matching relation row. Domain constraints check relation
keys against the preceding type parameters. Membership does not replace the
payload with a Boolean, and different family slots have distinct carriers.

Checked family applications keep their runtime indices through specialization.
The existing dependent sum and fibre rules then retain declaration/kind indices,
constructor guards and payload relationships. Calls and constructions pass the
same family bindings; mutual inclusion checks binding equality independently
of row order. Family relations have no finite-size constraint. Behavioral
callbacks, dependent argument domains within a family telescope, and unsolved
universe constraints remain unsupported by this rule.

`FamilyRelations` states general source and payload round trips, index
preservation, selection/wrapping preservation and transport across actual index
equality. These laws require a justified source/native family binding and do
not assume proof irrelevance. In the self model, `Obligations.Requirements.Evidence`
and its three nonrecursive selectors/wrappers are native. CI independently
parses their emitted SysML, checks every constructor and complete proof payloads,
rejects wrong indices/kinds/families/bindings, and detects removal of a binding
constraint. Recursive completeness carriers and higher-order validation remain
explicit boundaries.

Generated relation/member carriers are marked as generated provenance
boundaries rather than invented checked Agda declarations. Rendering a carrier
uses the complete carrier context to retain links to nested parameterized
members. Quantified row and list-element projections cast to their declared
element carrier before projection, as required by the pinned validator.

`Specialization` states general substitution, value round-trip, and operation
preservation laws for arbitrary named families and ordered type arguments.
Compiler de Bruijn substitution, discovery of concrete uses, and the target
instance-key correspondence remain implementation obligations.

The compiler's `Abs`/`NoAbs` flag determines whether a type codomain extends
the de Bruijn context. Compiled function bodies have a separate value-binding
environment. Projection-like functions can omit a leading prefix of type
parameters from both their body and calls; `projection.index` identifies that
prefix, and checked argument/result carrier unification recovers its concrete
types. Only resolved type binders are removed. A missing parameter, inconsistent
inference, unsupported dropped value argument, or runtime use of a type parameter is refused.

Instantiation precedes the existing finite/algebraic carrier and first-order
call gates. Cyclic carriers remain unsupported except for the builtin list rule.
Recursive helpers must retain the same static instantiation and pass the
termination and dependency checks below. Open mapping roles cannot be justified by
unrelated concrete uses of the same template. Constructor parameters omitted by
Agda are recovered from an expected result carrier or ordered payloads; a use
with insufficient type information remains incomplete.

The native evaluator checks distinct Boolean and enumeration instances, proper
projection-like calls, and payload selection. Independent expression-algebra
tests additionally cover returned construction, nested carriers, heterogeneous
type-argument order, phantom parameters, and static binder removal. The Pilot's
returned-construction limitation continues to apply.

## Static universe levels

Universe-polymorphic specialization retains both level and type parameters in
their checked order. Closed levels built from zero, successor, and maximum
resolve to arbitrary-precision natural numbers in instance identities. A level
argument is static metadata, not a target runtime carrier. Each concrete type
argument must inhabit the universe declared by its instantiated telescope.
Compiler builtin identity establishes `Level`; source spelling is insufficient.

Open declaration schemas also retain symbolic levels, successors and maxima.
Template level binders and rigid levels belonging to an open schema have
separate identities: substitution of a helper's arguments cannot capture a
level in its caller's scope. Normalization combines repeated atoms and removes
dominated constants while preserving distinct variables and their offsets.
Symbolic level expressions remain in specialization identities and provenance;
they do not become runtime inputs, type extents, or integer-valued fields.
Open type and family arguments must still have exactly the declared universe.
This supports the original polymorphic sequence operations and indexed-family
encode/decode operations without fixed-level source wrappers.

Omitted levels may be recovered from checked carrier universes and parameter
constraints only when those constraints determine them uniquely. Ambiguous,
unsolved, inconsistent, or runtime level uses remain incomplete. A declared
symbolic level is a bound parameter, not an unsolved inference variable.
Removing static binders must preserve all runtime values and their positions.
`UniverseLevels` gives general level substitution/resolution laws and runtime
environment reconstruction and lookup-preservation laws for this boundary.

The compiler retains registered `Level`/`LevelUniv` and level operations in source
provenance. Their static dependencies receive the `static.universe-level` rule
with no runtime target. Every consuming carrier and function must independently
pass specialization and native lowering; selecting a level declaration as a
runtime mapping root remains unsupported.

Native calculation input references are qualified by their declaring calculation.
This preserves the lexical input when a call or constructor introduces another
scope with similarly named inputs.

## Finite dependent indices

A nonrecursive family indexed by Boolean or closed enumeration values has its
own native carrier. Each constructor retains its tag and ordered payload, and
its result indices are computed from finite literals or finite payloads.
A member at a particular index is that carrier constrained by its index
projection. Function inputs and results retain those constraints, including
relationships to earlier runtime arguments. No universal value carrier is used.

Constructor dispatch may omit branches only when the checked finite index
constraints make them impossible. Branch-local index refinements must be
preserved when checking returned values and helper arguments. An unsupported
index expression, recursive family, or unsupported compiled
matching mode remains a diagnostic; an index cannot simply be erased to make a
signature admissible. `IndexedValues` specifies constructor/index preservation,
fibre round trips, dependent operation preservation, and payload dispatch.

The current indexed-family rule accepts datatypes with no remaining static
parameters, at least one constructor, and finite index telescopes. Constructor
payload types may use closed fibres or refer to earlier payloads through the
finite dependency rule described below.
Constructor result indices and function type indices are finite literals or
references to preceding runtime binders, proper projections, or admitted finite
helper calculations (see below). Concrete static parameters are specialized before this rule runs,
while runtime indices remain in the resulting telescope. Closed record fields
retain their fixed-index constraints.

Each carrier has singleton index fields constrained to the selected constructor's
result indices. Calculation assertions constrain indexed inputs and results.
The checked case tree retains every possible constructor; only incompatible
closed finite indices justify excluding a constructor. Symbolic branch
refinements substitute earlier input references, and calls check instantiated
fibre identities. Projection metadata can omit leading finite arguments from
calls/bodies; those arguments are recovered consistently from principal fibres
and remain explicit in the native calculation signature. Inference that cannot
establish a unique consistent index is refused.

A datatype used as a mapped relation keeps its existing relation representation;
it is not simultaneously emitted as a value carrier under the same target name.
Using one declaration in both roles is outside the current combined rule.

## Dependent record fields

An acyclic record may contain a field whose finite family index refers to
preceding Boolean or enumeration fields. The native record retains every field
and constrains the member's index projection to the corresponding earlier field.
Construction checks the ordered telescope after substituting preceding values;
projection and record matching substitute projections of the actual receiver.
Nested proper record projections and admitted finite helper calculations may
occur in index expressions.

`DependentRecords` quantifies over arbitrary preceding field tuples and dependent
members. Its round-trip, field, and operation laws govern this representation.
The adapter must validate proper projection ownership and declaration types;
field spelling alone cannot justify a dependent index expression.

The record rule checks every proper field declaration against its constructor
position after replacing prefix inputs with projections of the same receiver.
Forward references and mismatched owner/index relationships are refused. The
same substitution is applied to eta-expanded fields and helper results. A
projection of a known constructed record reduces to its declared field value
for type comparison. Finite helper expansion follows the separate admission rule
below. Unresolved static parameters remain a separate boundary.


## Dependent constructor payloads

A nonrecursive sum constructor may have later payloads whose finite family
indices refer to earlier payloads, including proper fields of an earlier record
payload. Each constructor has its own ordered telescope. Only preceding values
are in scope; forward references, unsupported computed indices, erased fields,
and recursive carrier dependencies are refused.

The native carrier retains optional slots for every constructor payload. Its
admissibility constraint requires exactly the selected constructor's slots and
no inactive slots. Index equalities are guarded by that constructor's tag, so
an inactive constructor does not impose relationships on absent values.
Constructor calculations retain dependent input constraints and result indices.

Construction substitutes each accepted payload into the types of subsequent
payloads. Case expansion substitutes projections of the selected constructor's
slots into each payload type before nested matching. Matching either an earlier
finite value or a dependent member refines the same branch environment; those
refinements must survive helper calls and reconstruction. The existing checked
case-coverage and arity gates remain mandatory. Concrete type/universe
specialization retains these relationships before native admission.

`DependentSums` quantifies over constructor tags, preceding payload tuples,
dependent members, observations, and operations. It proves both round trips,
tag and member-index preservation, dispatch, arbitrary result-index observation,
and operation preservation. Its payload correspondence composes with
`AlgebraicValues`' inactive-slot encoding and `IndexedValues`' result fibres.
The compiler's case extraction and the renderer's guarded optional-slot
constraints remain adapter obligations. The public `DependentPayload` contract
and semantic/refusal/native evaluation tests cover these boundaries. The
existing Pilot limitation for evaluating returned new constructions still
applies; the independent expression-algebra tests cover that lowering.

## Specialization of indexed families and dependent records

Leading concrete type and universe arguments compose with finite indexed
families and dependent record fields. A static family instance has one native
carrier for all its runtime indices. Specialization preserves ordered runtime
telescopes, constructor result indices, and receiver-specific projection types;
it removes only static binders. Proper field ownership is checked again by the
native record gate after specialized projection identities are substituted.

Static inference matches carrier structure to recover type/universe arguments.
Symbolic family arguments retain their lexical identity, index domains and
universe when recovering omitted constructor arguments. Within an indexed
family application, each index domain is instantiated with the preceding index
values before checking its argument. A member at a different preceding value
still fails that check.
It does not discharge runtime index equalities: those survive in the specialized
signature and must pass the native fibre checks. Projection-like functions may
omit both static parameters and leading runtime indices. The remaining metadata
preserves the runtime prefix for native argument recovery and body binding.
Finite constructor indices with omitted static parameters are resolved against
their expected finite domain, including specialized enumeration domains.

A fixed fibre can itself be a closed type argument, such as `Box (Evidence Bool
false)`. Its index is retained in the outer instance key and target name;
`Box (Evidence Bool true)` is a distinct instance. Runtime-dependent first-order type arguments use the captured-index rule below.
Arbitrary computed indices and unsupported higher-order behavior remain
outside this composition rule.

`SpecializedFamilies` states both round trips, index preservation, and operation
preservation for arbitrary static interpretations, index domains, preceding
field tuples, and members. Its equality premise is the interpretation equality
provided by static substitution/resolution. Correct compiler-term substitution
and native constraint emission remain tested adapter obligations. The public
`SpecializedIndexed` contract covers multiple universes, both finite index
kinds, dependent fields, and fixed fibres as static arguments; expression-algebra
refusal tests ensure specialization cannot hide inconsistent runtime indices.


## Computed finite indices

An index may invoke a checked, nonrecursive helper whose inputs and output are
Boolean or admitted enumeration domains. Inputs and output may have different
finite domains. A separate finite-only pass checks signatures, exhaustive bodies,
and the entire acyclic call closure before carrier discovery. A signature, opaque
body, recursive cycle, or unsupported callee cannot justify an index expression.
Proper record projections may supply finite arguments to these helpers.

Native index constraints retain named calculation calls. For type comparison,
the adapter expands only admitted finite helpers with capture-free input
substitution, reduces known-construction projections, finite literal equality,
and literal conditional guards, and compares the resulting expressions.
This is deliberately incomplete: unequal or still-distinct expressions produce
a diagnostic, even if a stronger theorem prover could establish their equality.
It does not invert a helper or assume injectivity. Branch equalities are retained
through subsequent construction checks; only proven literal incompatibility
removes an impossible branch.

Calls in input/result indices participate in calculation dependency reports and
closure checking. Static specialization retains computed index syntax and clones
helpers reached solely from a type. Runtime indices do not become static family
parameters. Arbitrary computation, infinite domains, recursion, and higher-order
index functions remain outside this rule.

`ComputedIndices` proves substitution preservation and native index evaluation
for admitted acyclic programs, sound comparison given justified expansion, and
dependent transport under branch equality. These are general laws; extraction,
normalization, and compiler binding correspondence remain implementation
obligations. The public `ComputedIndex` contract combines finite helper chains,
Boolean-to-enumeration calculations, indexed sums, and specialized record fields.
Implementation tests check evaluation and refusal; native tests check helper
results and valid/invalid computed constraints.


## Computed structured indices

After carriers are admitted, a separate pass can admit acyclic native
helpers over those carriers. Indexed families consuming their results do not
justify their own helpers. Every helper still needs a supported body and complete
call closure; a signature alone is insufficient.

Checked recursive helpers with indexed inputs or results, such as the existing
`schemaAt` lookup and `absent` slot constructor, may also appear in indices after
their carriers are admitted.
They require safe-module termination evidence and a supported complete call
closure. Symbolic comparison unfolds a recursive symbol once along each path
and leaves further calls opaque; native emission retains the recursive call.
Constructor facts apply to the expressions exposed by unfolding. If a recursive
helper still has an unknown outer branch, comparison retains the call, allowing
both sides of a recursive equation to meet at the same residual lookup.
This bounded comparison does not assume injectivity or prove arbitrary recursive
equations. Unindexed recursive helpers continue to require the concatenation
certificate below.

A recursive list helper has a finite concatenation normal form only when its
checked native body matches both constructor equations: the empty branch returns
the second input, and the prepend branch retains the head and recursively joins
the tail with the second input. Applicability uses checked shapes, signatures,
case semantics and safe termination evidence; it does not inspect function names.
Other recursion without indexed inputs or results remains unsupported.

Comparison uses the certified concatenation form, flattens nested ordered
sequences, and handles empty contributions. List indices compare their contents;
existing type/family binding checks remain. This permits dependent field append
without inferring a split of inputs from an equal concatenated result. Native
calculations and constraints retain the original helper calls and their lexical
parameter bindings. No normalization evaluator is embedded in the target.

This supports the existing `AlgebraicValues.slotAt`, `sourceConstructor` and
`nativeConstructor` operations directly. A chosen tag computes the required
payload schema; source and native construction preserve every payload field,
and native construction retains the `Active` validity evidence. Lookup returns
the selected slot, including `nothing` for an inactive slot. Fixed fibres used
as static type arguments may be compared through checked source reduction;
blocked computations remain distinct, and target checking still verifies their
runtime indices. No project-specific declaration names are used by these rules.

The parsed-SysML checks exercise every position in several schemas, including
equal schemas at different constructor positions, empty and repeated fields,
open payload families, and unbounded natural atoms. Wrong payload schemas,
wrong tags and mismatched slot schemas must fail emitted constraints.

`SchemaConcatenation` proves the characterization, source/native correspondence,
and associative grouping laws for arbitrary atom carriers and finite lists.
The adapter must establish the equations from the checked body. Tests exercise
arbitrary helper names, altered equations, missing bodies/termination evidence,
and refusal to recover ambiguous inputs, alongside complete field results from
the project's own `append` and `nativeAppend` emitted as SysML.

## Naturals, ordered lists, and checked recursion

The registered builtin natural carrier maps to `ScalarValues::Natural` with
finiteness constraints at value boundaries: KerML's Natural also contains
infinity. Canonical Agda primitive identities and exact signatures admit
addition, multiplication, truncated subtraction, equality, and comparison.
Successor and natural case analysis retain zero and predecessor semantics.
`NaturalValues` proves both carrier round trips and the operation laws for every
natural. No machine-integer bound is imposed on source or target values.
Its existing `encode`, `decode`, `successor`, `add`, `multiply`, `subtract`,
`equal`, and `less` operations translate directly. Parsed SysML tests retain
the complete finite-value evidence, exercise large integers, and reject
infinity, negative values, missing evidence and inconsistent evidence indices.

The pinned Pilot stores integer literals as Java `int`; its evaluation is not
an arbitrary-precision arithmetic oracle. The renderer decomposes large literal
constants into arithmetic with bounded lexical literals. Native numeric tests
use the evaluator's supported range, while independent expression tests cover
large integers. This workaround does not establish that Pilot can execute every
mathematical natural operation.

Concrete builtin lists use a domain-specific wrapper with an ordered, nonunique
`items` feature and a finite-size constraint. Empty and cons retain order and
duplicates. Case payloads use native head and tail operations; a head is cast to
the checked element type before feature access. The cast is justified by the
wrapper's element declaration and is used only in the nonempty branch.
`SequenceValues` proves round trips, length, append, and case preservation.

Recursive call components require positive Agda termination results from modules
checked with both safe mode and termination checking enabled. A function flag
alone is insufficient. Every member's body and every outgoing dependency must
be admitted. Failed members are removed to a fixed point, preventing a temporary
cache entry from admitting a broken cycle. `RecursiveCalls` proves preservation
by accessibility induction, conditional on step correspondence. The compiler
adapter must justify that the checked source termination result applies to the
specialized calls. Computed-index comparison uses the bounded expansion rules
described above.

## Record updates, value parameters, and closures

Checked record copatterns become a native record construction with one expression
per declared field. Exact field coverage and projection arity are checked.
Nested failed constructor matches use the enclosing fallback with its original
binding environment. Unused fallback trees need not acquire an independent
executable representation. `DecisionTree.fallback-preserves` states the general
fallback law.

Runtime value parameters of admitted datatype families remain explicit family
indices and constructor inputs. Agda omits declared parameters from constructor
terms and case payloads; the contextual expected family supplies them. Native
fibre checks still enforce the result relationship. Indexed records, arbitrary
index computation, and unresolved constructor contexts remain boundaries.

Concrete function arguments are specialized into first-order helper instances.
Free runtime variables become explicit input parameters; their values are not
part of the specialization key. Capture-avoiding substitution replays checked
case bindings and eta-short leaves. Closed static arguments retain their type
and universe meanings. Recursive calls reuse the same closure template; changing
instantiations and dependent closure signatures remain unsupported. The target
contains no closure objects or Agda evaluator.

Known constructor arguments may also be specialized when their record or
datatype contains callbacks that have no admitted native carrier.
The checked case tree selects the known constructor, retaining runtime cases
and specializing recursive calls at their remaining known containers. Every
free runtime value inside the container becomes an explicit capture input;
capture values do not enter the specialization identity. Helpers retain the
type bindings needed by their captures, ordinary inputs, and full results.
First-order container indices may refer to earlier explicit inputs. Their
positions are transported into the generated telescope. A known constructor
can establish an index equality; that equality is retained as a native
precondition as well as used for branch checking. Invalid bindings therefore
remain rejected. Boolean/finite lowering and index-helper expansion cannot
silently discard these additional preconditions.
Nested constructor indices receive their declared type context, including
empty schemas whose element types cannot be inferred from payloads.

The self specification exercises this through `DecisionTree.choose`,
`DecisionTree.guardedValue`, and `AlgebraicValues.constantDispatch`. Their
outcomes are arbitrary domain values. Guard failure preserves the absent
result, and constructor dispatch preserves the selected complete outcome.
This specialization rule supports concrete uses of the original evaluators.
The separate callable-member rule below admits supported supplied containers.
Unsupported unknown containers, dependent function-valued result families,
opaque or unchecked helper computations remain refusal
boundaries. Static callback expansion is bounded to 128 active helper frames;
exhausting that bound refuses rather than assumes semantic preservation.

## Native unary and multiargument callback inputs

A checked function input is represented by a native `in calc` usage with an
ordered argument telescope and one typed result. This includes `A → B`,
`A → B → C`, and dependent signatures such as `(a : A) → B a → C a`.
Fully applied calls invoke that usage
directly. Passing the input to another admitted operation preserves the same
binding, including through recursive helpers. The compiler checks both domain
and result types before admitting an application; it retains open type extents,
record payloads, indices and result contracts.

The binding must denote a total, deterministic, side-effect-free mathematical
function, as required when using SysML calculations mathematically. Each argument
and the result have multiplicity one, their declared carriers, and the applicable
native extent/refinement constraints. These contracts do not prove purity or
termination of an arbitrary externally supplied calculation. No function table,
Agda value encoding, or target interpreter is emitted. See the native invocation
mechanism in [KerML 1.0 §7.4.9.4](https://www.omg.org/spec/KerML/1.0/PDF) and
calculations in [SysML 2.0 §7.19](https://www.omg.org/spec/SysML/2.0/Language/PDF).

This rule covers callbacks with supported first-order domains and results,
including indexed families. Callback arguments have their own indexed lexical
scope. Each argument domain is instantiated with preceding supplied arguments;
the result is instantiated with the complete argument list. Implicit value
indices are retained as explicit SysML arguments.
Signatures retain references to surrounding inputs and earlier record fields,
including calls to supplied callbacks inside an index. Substitution resolves a
callee's index telescope before inserting caller types, so indices inside those
types cannot be captured accidentally.

Callbacks that take function-valued arguments, runtime type-polymorphic callbacks,
and runtime closure construction remain outside this rule. A partially applied
callback is refused when it requires creating a closure; overapplication is
rejected by the result type. Function-valued family indices are explicitly refused:
family indices are data attributes, and function identity needs a separate
representation and equality rule. Stored callbacks and their projections use the separate
callable-member rule below. Existing static closure
specialization continues to handle supported concrete callbacks separately.

The self specification exercises the rule through `BooleanLowering.map`,
`Diagnostics.Accounting.mapEntry` and `mapReport`, `Diagnostics.Located.annotate`,
`NaturalValues.caseNat` and `nativeCase`, and `SourceAlignment.Direct.mapMaybe`
and `rename`. Tests vary supplied calculations, preserve complete evidence and
opaque payloads, and use unbounded natural extents.

The multiargument rule also translates the existing `ComputedIndices.replace`
and `replaceArgs`, `DependencyScope.evaluate` and `evaluateArgs`,
`Derivations.Trace.combine`, and `SequenceValues.caseList` and `caseSequence`.
Their tests exercise dependent substitution, argument order, complete values,
metadata preservation, invalid bindings, and deliberate body mutations.

**Pilot execution limitation:** the pinned Pilot 0.58.0 validates this native
representation, but invocation through a bound callback can remain an unresolved
`InvocationExpression` even when direct invocation of the supplied calculation
works. Interactive callback execution is therefore not supported by this pinned
toolchain. The independent test oracle parses the emitted SysML, invokes supplied
native calculations, and checks complete results and contracts; this is distinct
from official Pilot execution. Pilot can also report incompatible callback
bindings as warnings, so validator acceptance alone is not refusal evidence.

## Native callable members

Records and constructor payloads may contain supported unary or multiargument callbacks,
including indexed and dependent signatures. A member is emitted as `ref calc` with explicit argument/result types,
multiplicity and extent/refinement constraints. The containing carrier remains an
immutable `attribute def`. The member is referential and nonvariable; it does not
give the container occurrence identity, ownership, or a lifecycle. This follows
the referential-feature requirement in
[SysML 2.0 §7.7](https://www.omg.org/spec/SysML/2.0/Language/PDF) and data-value,
construction, and feature-chain invocation semantics in
[KerML 1.0 §§7.4.2 and 7.4.9](https://www.omg.org/spec/KerML/1.0/PDF).

Native constructor bindings retain callable references. Record projections and
constructor splits recover them with their checked signature; applications use
native member invocation. Each callable member has a typed `.invoke` calculation
that binds the receiver before invoking its member. This supplies the feature
chain required by SysML syntax even when the caller computes the receiver, and
retains the selected-branch guard and singleton-member precondition. A proper
Agda projection's telescope ends at its
record receiver, so any subsequent function arrow describes the member value.
Returning that member uses `return ref calc` with its signature and contracts.
Reconstruction forwards the same reference, and recursive helpers retain its
lexical type bindings. Sum validity still requires exactly one value in each
selected payload slot and no values in inactive slots.

The original `DecisionTree.evaluate`, `evaluatePartial`, `select`, and
`withFallback` operations exercise this rule on supplied runtime values.
`select` preserves first-match priority and absent results; `withFallback`
reconstructs trees while preserving their guards and effects. Outcomes remain
complete domain values. The parsed-model tests cover these behaviors, malformed
members, and incompatible bindings.

`FirstOrder.lookup`, `nativeLookup`, `evaluate`, `evaluateArgs`, `nativeEvaluate`,
and `nativeEvaluateArgs` use indexed callback signatures. Tables retain supplied
calculations; expression evaluation invokes table entries or the calculations in
an `Operation` record. The record also retains its `operation-preserves` member:
a dependent callback returning a complete equality-evidence value. Its endpoints
contain calls to `sourceOperation` and `targetOperation`, with `encodeFields`
connecting their input representations. This evidence is not replaced with a
Boolean condition or removed from the record. Callback argument/result contracts
retain the signature's input schema, output index, and evidence endpoints.

The callback-input purity/totality obligation and Pilot execution limitation
above also apply here. Supported lambdas can construct new callbacks through
the native body-expression rule below.
Direct sequences of callables
and recursive carrier cycles through a callable's domain/result remain outside
the rule. No generic Agda evaluator or callback table is emitted.

## Captured lambdas

A checked lambda with a supported, complete callable telescope becomes a
native SysML body expression: `{ in argument : Domain [1]; return result :
Result [1]; expression }`. The expression retains references to the enclosing
calculation's values, supplied callbacks, and type/family bindings. Its local
parameters have distinct lexical names; nested lambdas and unused Agda
`NoAbs` binders retain the correct enclosing environment. Calls within the body
remain ordinary native calculation dependencies.

This uses [KerML 1.0 §8.4.4.9.3](https://www.omg.org/spec/KerML/1.0/PDF): a body expression denotes its evaluation rather
than immediately returning the body's result. Record fields remain referential
`ref calc` members. No domain-specific closure datatype or Agda evaluator is
introduced. The containing callable signatures retain their argument, result,
and extent contracts.

The unchanged `DecisionTree.restrict` constructs guards that combine a captured
predicate with each existing guard. `normalize` builds ordered rules from a
tree, including the complementary guards for negative branches. Their
`restrict-true`, `restrict-false`, `normalization-preserves-evaluation`, and
`normalization-sound` statements become native constraints; this does not
translate their proof implementations. Independent emitted-model checks retain
callbacks from distinct invocations, compose restrictions, compare complete
outcomes, and reject inconsistent premise evidence.

The same rule admits `AlgebraicValues.tabulate`: a callback supplies each field
by its typed position, and a captured callback transports the remaining
positions through recursive calls. Repeated field types retain distinct values;
the supplied family bindings and complete membership evidence remain present.

Partial applications requiring eta expansion, runtime-polymorphic lambdas,
function-valued indices, and extensional equality of newly constructed
callbacks remain unsupported. The pinned Pilot validates body expressions and
their use in records; its existing callback-execution limitation still applies.

## Stored type and type-family fields

A record's declared parameters and its actual fields have different scopes.
A field of type `Set`, or an independently indexed first-order family ending in
`Set`, is retained as a runtime schema binding. It is not mistaken for another
static parameter of the record constructor. Proper projections must still agree
with the constructor telescope, including which earlier field they select.

The binding is an immutable attribute value containing unordered relation rows.
Each row retains every index and the complete member payload. A value belonging
to that family carries the binding, its indices, and its payload; its constraint
requires a matching row. A type field uses the same representation with no
indices. Extents are not ordered source lists and have no imposed finite-size
constraint. Reordering rows preserves the binding's meaning. Substituting a
different extent or changing an index or evidence payload does not.

A stored family's index domains may select earlier fields of the containing
record. Those values become explicit captures of the binding and its rows.
Membership checks compare captures as well as indices and complete payloads;
an empty extent still has to satisfy its capture contract.

A named nonrecursive record family can also construct a stored binding.
Native collection expressions enumerate supplied type/family extents and finite
constructors, retain complete record values, and filter constructor index
equations. Fixed indices recover corresponding constructor fields, including
equality evidence. This rule does not invent finite bounds for natural numbers,
enumerate recursive payloads or arbitrary callbacks, or replace evidence with
Boolean flags. Available extents must cover every otherwise free payload domain.

Conversion between a concrete record and a stored-family member requires
checked definitional reduction identifying that record family. Constructor
branch equations may resolve duplicated implicit indices, using constructor
injectivity; computations are not assumed injective. A recursive unary list map
can serve as a computed index only when its checked body recurses exactly on the
tail and computes each output head solely from the corresponding input head and
static bindings. The original recursive calculation remains in the output.

Dependent callback signatures retain selections from those stored bindings.
When a callback's result specializes another carrier at a callback-local index,
that index becomes an explicit captured value of the specialized carrier.
It remains bound within the callback signature and cannot be confused with an
outer input. Generated schema carriers have generated provenance boundaries;
the containing declarations, calculations, and contracts retain their source
correspondence.

The self specification exercises this with `OpenParameters.Transport` value and
list conversion and `FamilyRelations.Transport` indexed conversion, selection,
and reindexing. Complete membership and equality evidence remains part of the
model. Runtime-polymorphic callbacks and function-valued indices remain outside
this rule. Supplied callable references are
retained; the rule does not establish extensional equality between different
callbacks. The existing Pilot callback execution
and unordered data-value equality limitations still apply; independent behavior
checks are separate from official model validation.

## Checked reduction and retained source dependencies

Demand-driven reduction follows transparent, terminating checked definitions,
beta reduction, constructor projections, record eta, copattern selection, and
exhaustive identity cases. It neither assumes proof irrelevance nor classifies
fields by spelling. A projection may discard an unused evidence field because
of its checked computational definition. Bounded reduction may refuse; exhausting
the budget is never semantic evidence. `DefinitionalReduction` states the
reduction, projection, closure, and record-field laws.

For module-copy constructors, the inventory retains Agda's canonical constructor
head. Specialization follows that checked identity before emitting a constructor,
even when the alias's signature can already be read. Reduction preserves the complete payload
spine. It does not guess omitted phantom module parameters from names or choose
an arbitrary type to fill them. Missing identity metadata and abstract aliases
remain refused.

The report retains the original conservative dependency obligations. After every
selected root and its entire prepared dependency graph pass native admission,
source-only dependencies outside that graph can satisfy a `reduction-source`
requirement under `source.reduced-dependency`. `sourceKind` records the original
role; the checked declaration, source, assumptions, and untranslated reason remain
available. Such an entry has no native target and is not reported as translated
behavior. An explicitly selected root or any unresolved runtime dependency cannot
use this rule. Missing root preparation disables this accounting rule entirely.

`runtimeDependencyClosure`, `runtimeDependencyClosureVerified`,
`retainedReductionSources`, and `preparationEvidence` make the distinction
inspectable. `DependencyScope.footprint-sufficient` proves that changing unused
function-table entries cannot change a term's result; its composition law also
requires equality between the original computation and its reduced form.
These laws do not constitute an end-to-end proof of the Haskell adapter or SysML
renderer. Source-to-checked occurrence precision remains separately reported.


## Safe inductive recursive carriers and natural indices

A recursive datatype component is admitted only when its original module was
checked in safe mode with positivity checking enabled. Records, coinductive
values and changing static recursive instances remain outside this rule. A
provisional header permits checking mutually dependent constructor telescopes;
a failed root rolls back its entire preparation attempt. Nested acyclic instances
of one template do not constitute a recursive component.

Each native value retains its constructor tag, every payload, and every index.
A generated finite natural node count equals one plus the counts of its direct
children in the recursive component. Each child count is smaller than its parent.
These guarded constraints exclude cyclic native values. `RecursiveValues` proves
constructor-tree round trips, tag/payload/count preservation, and the general
child-decrease law. `NaturalIndices` proves that every source finite ordinal is
below its context bound and every source vector length equals its index.

Natural zero/successor indices remain native natural expressions. Checked case
branches refine constructor fibres; a positive natural branch justifies the
predecessor/successor equality only inside that branch. Inherited equations are
rebased through subsequent splits. An absurd leaf is admitted only after the
refined environment contains a carrier fibre with no possible constructor.
Checked natural primitives also retain their value-argument telescope when
used in dependent indices. Native helper expansion traverses arithmetic operands;
addition flattens nested sums and combines constants while preserving the order
of symbolic operands. A positive-branch predecessor/successor equation can then
justify an index comparison without escaping that branch. Arbitrary arithmetic
identities and injectivity of unknown calls are not inferred.

Dependent matches also retain facts about constructed, non-indexed values used
as indices. A preceding witness match can establish the tag of such a value;
a later lazy split then uses that known tag instead of requiring every constructor
of its declared datatype. Equal record constructions, or equal constructions
with the same datatype tag, establish equality of corresponding payloads. This
decomposition requires the same carrier and ordered fields. It does not infer
injectivity of arbitrary helpers or permit an ambiguous lazy split. Facts remain
local to their branch and the particular values they describe.

These rules admit the unchanged `RelationBindings.lookup`, `position`,
`boundValues`, `embed`, `evaluate`, and `lower`, together with `Sharing.expand`
and `Derivations.Trace.Readiness.combine-ready`. They also make six existing
preservation statements native constraints: `lookup-preserves`,
`nonbinding-preserves-position`, `endpoint-preserves`, `equation-complete`,
`equation-sound`, and `Sharing.reconstruction`. Their Agda proof implementations
remain separately accounted for. The emitted-model checks compare complete
contexts, values, layouts, trees, and readiness evidence; exercise both binding
and nonbinding slots; and reject mismatched indices and evidence. Compiler-shaped
regressions also reject a lazy split with no established constructor and prevent
one input's witness from refining an unrelated input.

This admits the unchanged `CapturedIndices.append`, `captureSlot`, and
`runtimeSlot` calculations, their two lookup statement constraints, and
`Derivations.shift-order` and `Trace.shift-preserves-bounds`. Complete vectors,
ordinal values, spans and order evidence remain in the native result. The
independent emitted-model checks cover unequal context sizes, repeated opaque
payloads, large natural endpoints, and inconsistent indices and evidence.
The same rules admit `RecursiveValues.left-bound` and `right-bound`, the
`Trace.length-append` statement, and the five binary arithmetic/comparison laws
in `NaturalValues`. These statements remain separate from their retained Agda
proof sources.

For ordinary sum carriers, a checked constructor branch also establishes its
tag. When such a value indexes another carrier, incompatible constructor tags
can establish an empty fibre. This fact is local to that scrutinee and branch;
an unknown payload or an unrelated input cannot establish impossibility.
Lazy matches require a record or a uniquely determined constructor.

## Captured runtime indices in type arguments

A static type expression can contain runtime indices, for example `Vec (Expr m)
n`. The specialization key abstracts those values into ordered captured slots;
its native carrier retains both the captured `m` and the ordinary `n`. Closed
fibres retain their distinct concrete specialization identities. Captured values
precede ordinary helper inputs, and calls supply the actual values at that prefix.
Constructor contexts restore value parameters omitted by Agda's checked terms.

`CapturedIndices` proves that lookup into either part of a prefixed environment
returns the original value, universally over both context sizes, environments
and value types. The concrete compiler extraction, rebasing and constraints are
implementation obligations. CI parses the actual emitted compiler-core carriers
and `lookup`, `remove`, `source`, `target`, `lower` bodies. It compares complete
results, including non-identity substitutions and unequal context sizes, rejects
invalid bounds/counts/bindings, and checks a removed-captured-constraint mutation.
Unsupported indexed records, index calculations and higher-order signatures
still produce explicit refusals; this rule does not encode a general Agda evaluator.
