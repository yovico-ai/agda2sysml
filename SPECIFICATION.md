# Agda to SysML specification

Status: initial specification for review. Requirements describe the intended
generator; the accompanying Agda modules establish the formal core identified
below. A generator is not yet implemented.

agda2sysml generates SysML models and a source-linked definition inventory from
Agda specifications. The purpose is to make structures, operations, conditions,
effects, and formal contracts inspectable while retaining the meaning and limits
of the source. Agda supplies behavior. A project mapping supplies modeling roles.

## Scope and authority

The generator will be implemented in Haskell using an explicitly supported Agda
compiler version. It will target SysML 2.0 textual notation. Exact compiler API
and SysML validator dependencies must be pinned before implementing their
adapters. The formal core currently checks with Agda 2.8.0 and uses only Agda
builtins; this does not establish a generator compatibility matrix.

The [project mapping contract](docs/project-mapping.md) specifies configuration
version 1. The [formal specification](spec/README.md) defines general laws and
their proof boundaries. These contracts govern implementation. A disagreement
between written requirements and the formal model must be resolved explicitly;
neither may be silently weakened to match an implementation shortcut.

This initial scope includes structure extraction, two behavioral encodings,
contract presentation, source traceability, and coverage reporting. Interactive
rendering, hosting, application code generation, and automated correction of an
input specification are separate work. A downstream viewer can consume the
generated model and inventory without becoming the authority for behavior.

## Inputs and generation stages

The input consists of an Agda library, one or more entry modules, a versioned
project mapping, and the library dependencies needed to check those modules.
The requested entry modules and their import closure define the inspected
corpus. An unimported source file is outside this invocation's scope, not
silently counted as covered. The manifest must identify this scope.

Generation has five stages:

1. Check the input using Agda, resolve imports, and inventory declarations.
2. Resolve and validate the mapping against those checked declarations.
3. Extract source expressions and lower supported encodings into a typed
   intermediate model with provenance.
4. Translate supported intermediate constructs to SysML and validate the result.
5. Produce the model, definition inventory, diagnostics, and build manifest.

The compiler adapter must retain both checked identities and source-level
structure. Normalization may help establish equality, but must not erase a
declared abstraction, premise, proof dependency, or source name from the
presentation merely because the compiler can reduce it.

A checking or mapping error prevents emission of a successful model bundle.
Unsupported translation is a distinct outcome: a diagnostic presentation can
still account for the checked input without claiming a complete translation.

## Project mapping responsibilities

Mappings identify states, commands, transition entry points, outcome
interpretations, principal invariants, and theorem selections. They may supply
display titles and group definitions into models. They must not contain copied
transition tables, guard expressions, effect expressions, or proof statements.

Every semantic reference must resolve uniquely in the checked Agda scope. Two
import paths naming the same canonical declaration count as one candidate.
Multiple distinct candidates are an error; source order never breaks the tie.
Resolution success alone does not establish role compatibility.

The validator checks signatures and shared typing context. For example, the
selected transition must accept the selected state, and its result must be
accepted by the state projection. Typechecking must account for implicit
arguments and dependent indices. An unsupported signature is reported as such;
matching a function name or arity is insufficient.

Reusable adapters interpret encoding patterns. Adapter behavior must not branch
on a project's repository name or particular domain symbol names. Onboarding a
project using a supported encoding should require only mapping declarations.

## Definition inventory and structure

Each source declaration in the inspected corpus receives a canonical identity,
kind, declared signature, source span, owning module, and resolved references.
The inventory distinguishes project definitions from dependency definitions.
Dependency definitions needed to understand a generated element remain linked.
Re-exports reference an existing canonical identity rather than inventing a
second definition.

Records, data constructors and their payloads, fields, type parameters, function
signatures, and module relationships form the structural input. Constructor
payloads must retain their order and dependency relationships. A data type with
payloads cannot be represented as a payload-free enumeration.

Compiler-generated declarations must be associated with their source origin and
classified as generated support. A generated helper whose body contributes to
behavior is still a semantic dependency. Local declarations remain reachable
through their enclosing source declaration even when they have no stable public
Agda name.

An Agda record does not by itself establish SysML containment or ownership.
Structure extraction must preserve fields and references without inventing
business relationships. A richer mapping profile can be specified later.

## Executable transition functions

The function adapter interprets a total function over a command, a before-state,
and any additional inputs. It retains the whole outcome, including refusal
reasons, returned values, and the state determined by the selected projection.
An outcome label is presentation metadata and cannot establish state preservation.

Finite control structure is represented as a decision tree. A branch evaluates a
predicate; a leaf produces an outcome. Pattern matches must preserve their
bindings and dependent refinements. Failed matches, earlier conditions, and
catch-all branches must be represented so that the same input selects the same
leaf. Generated helpers from `with` expressions must remain associated with the
original control structure.

The formal normalizer converts this tree into an ordered list of guarded rules.
The true subtree is restricted by the predicate and the false subtree by its
negation. Selection returns the first enabled rule. For every tree and every
input, selecting its normalized rules returns exactly the tree's outcome.

The initial theorem concerns finite Boolean decision trees over arbitrary input
and output sets. Agda case trees with bindings, recursion, or proof-only branches
require an adapter correspondence argument before that theorem applies. The
adapter must not replace proof inhabitation with an invented Boolean test.

Source helper functions stay named in the intermediate model. Supported bodies
can be expanded on demand. Recursion is preserved as a recursive definition,
not unfolded to a fixed depth and then presented as complete behavior. Resource
limits produce explicit incomplete extraction diagnostics.

## Indexed transition relations

The relation adapter interprets constructors of an indexed data type as rules.
Each rule retains its constructor arguments as witnesses, its premises, and its
source and destination expressions. Parameters and indices must be distinguished;
their positions are defined by the mapping contract.

A rule permits an edge when a witness satisfies its premises and its endpoint
equations. The target semantic edge retains those equations and premises.
The formal core proves both directions: every source edge has a target edge,
and every target edge is permitted by the source rules.

Several enabled constructors remain several alternatives. Rule order must not
introduce priority or select a single result for a relation. The model does not
assume that a relation is deterministic, total, finite-state, or decidable.
Recursive premises remain recursive premises; the generator does not search for
all inhabitants or enumerate all reachable states.

## Guards and effects

Guards retain branch conditions, pattern refinements, quantifiers, and referenced
predicates. A summary may display predicate names with links to definitions;
it must not remove a conjunct while describing the result as the full guard.
Boolean checks and propositional premises remain distinguishable.

Effects retain before/after expressions and complete result values. A record
update supports a direct statement that fields not updated are preserved.
Claims about unchanged members inside an updated collection require the helper's
semantics or an applicable theorem. The generator must not infer those claims
from the top-level field name.

Operations such as lookup, filtering, mapping, and folding retain their ordered
collection semantics. Mapping a list to an unordered set is permitted only when
the relevant translation rule establishes that order and multiplicity do not
affect the represented behavior.

Atomicity, external side effects, persistence, and concurrency guarantees may be
presented only to the extent they are expressed in the input contract. A single
pure state update does not by itself establish an implementation transaction.

## Dependent constraints and contracts

Dependent arguments and indices contribute explicit constraints to the
intermediate model. A supported translation must preserve their relationships
and quantification. Unsupported dependencies retain a formal textual view and
block a complete semantic translation of every element that relies on them.

Selected invariants and theorem statements are displayed with all binders,
premises, conclusions, and referenced definitions. Proof bodies and supporting
lemmas remain available through dependencies. An invariant selected in a mapping
is a predicate of interest, not automatically a proven property of every state.

A theorem's reference to an operation is not itself a correctness theorem for
that operation. Stronger labels such as preservation or isolation require a
recognized statement shape with the actual assumptions retained. User-supplied
titles cannot upgrade the strength of a claim.

The inventory records whether the input was checked safely and whether its proof
closure depends on postulates or unsafe features. Such declarations may be
presented as assumptions or qualified claims. They must not be described as
unconditionally established safe proofs. A generated SysML constraint is also
not evidence that a SysML tool has proved it.

## Translation status and diagnostic behavior

Every definition receives a representation status and a display role. Display
roles such as domain element or supporting lemma do not remove the coverage
obligation. Representation status is either translated, with a rule identifier
and correspondence obligation, or textual, with a source-linked reason.

Textual coverage means the reader can inspect the definition and the reason for
the boundary. It does not mean equivalent SysML semantics were generated.
Diagnostic codes distinguish unsupported syntax, unsupported semantics,
unsupported target representation, and interrupted or resource-limited work.

A definition is semantically translated only when its required dependencies are
also accounted for by applicable translation rules. A named call to an opaque
helper may support navigation but cannot conceal an untranslated guard or effect.
Recursive components require a correspondence argument for the component; a
cycle of optimistic status flags is insufficient.

The tool has two specified generation modes:

- **Strict:** emit a successful bundle only when every required entry in the
  declared translation scope has translation evidence. A textual required entry
  prevents success.
- **Diagnostic:** emit supported elements and all textual boundaries, clearly
  mark the bundle incomplete, and retain the full inventory. This does not count
  as a successful strict translation.

Both modes retain inventory entries for all inspected declarations. The manifest
lists the required translation scope separately from the inspected corpus:
selected models and contracts plus their semantic dependency closure. Other
inspected declarations remain accounted for, but cannot inflate a claim of full
semantic coverage. The coverage report gives counts for each scope and status.

Diagnostics contain a stable code, source or mapping location, affected symbol
and model, and the reason the operation failed or remained textual. A fatal
configuration error must not fall back to guessing a project convention.

## Generated artifacts and reproducibility

A bundle contains SysML text, the definition inventory, source correspondence,
diagnostics, and a manifest. Source correspondence records which source clauses,
constructors, and expressions justify each generated element. The output must
be accepted by the pinned target validator before it is called valid SysML.

The manifest records entry modules, input digests, mapping digest and version,
generator and Agda versions, dependencies, target language and validator versions,
generation mode, scope, and completeness. It records a Git revision when present;
dirty files require content digests and must not be represented as an unchanged
commit. A non-Git input remains supported through content identities.

The same checked inputs, mapping, and toolchain must produce the same semantic
content and stable identifiers. Unchanged qualified declarations retain their
identifiers when unrelated files move or gain lines. Source locations may change;
line numbers are not element identities. Renaming a declaration may change its
identity. Wall-clock timestamps must not determine semantic output or ordering.

Source links may address bundled relative paths or an explicitly configured
source URL. The generator must not infer that a local repository is public,
upload sources, or silently embed absolute local paths or credentials. Hosting
and publication are explicit downstream actions.

## Formal correspondence and implementation obligations

The current core proves candidate-resolution properties, role-validation
consistency, decision-tree normalization, relation-edge preservation, and
inventory accounting with strict rejection of textual entries. See the
[proof coverage table](spec/README.md#proof-coverage).

These proofs are quantified over semantic input models. They do not prove the
Agda compiler adapter, YAML parser, Haskell implementation, SysML emitter, or
target validator correct. In particular, the formal edge model is not an
implementation of the SysML metamodel.

Each implementation component must state how its representation corresponds to
the formal domain. Every translation rule needs a documented semantic contract,
including its supported expression forms and failure behavior. The initial
correspondence work must cover the two adapters and the target rendering rules
before describing a complete end-to-end translation as verified.

Implementation tests exercise parser failures, compiler syntax variations,
target validation, and observable results. Differential checks can compare
executable Agda behavior and normalized rules for concrete inputs. These are
supplementary evidence, not substitutes for the general laws.

## Acceptance criteria

The first generator implementation is acceptable when:

- Independently authored projects using both transition encodings can be mapped
  without project-specific Haskell branches.
- Mapping validation reports unresolved, ambiguous, and incompatible references
  without guessing, and preserves dependent typing requirements.
- Commands, payloads, conditions, refusal precedence, effects, and relation
  alternatives are accounted for with exact source correspondence.
- Unsupported behavioral dependencies prevent strict success and remain visible
  in diagnostic output; no input declaration silently disappears.
- The generated SysML passes its pinned validator, and the inventory and source
  references have no unexplained omissions or broken local targets.
- Repeating generation on identical inputs gives the same semantic artifacts.
- The formal aggregate type-checks safely, and the adapter and emitter
  correspondence obligations have explicit evidence or stated limitations.

Exact CLI spelling, serialized inventory schema, diagram layout, the first
concrete SysML validator release, and the full target expression subset remain
implementation-design decisions to specify before those interfaces are built.

## References

- [OMG SysML 2.0 specification](https://www.omg.org/spec/SysML/2.0/)
- [Agda 2.8.0 safe mode](https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html)
