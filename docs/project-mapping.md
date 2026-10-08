# Project mapping version 1

This implemented configuration format identifies the roles of checked Agda
definitions. The alpha supports both this version and
[version 2](project-mapping-v2.md); translation support remains subject to the
[documented rules](translation-rules.md).

The conventional filename is `agda2sysml.yaml`. The
[complete illustrative mapping](examples/agda2sysml.yaml) describes a fictional
project with a function-based review machine and a relation-based workflow.
Its symbols are illustrative; it is not a compilable Agda example or an installed
configuration for this repository.

## Document shape

The root mapping has exactly three keys: `mapping-version`, `project`, and
`models`. Version 1 requires the integer `1` as `mapping-version`. Unknown keys,
duplicate keys, unknown versions, null required values, and incorrect scalar
types are configuration errors. The parser uses YAML 1.2 core scalar semantics.
Custom tags, aliases, anchors, and merge keys are outside version 1 and must be
rejected explicitly rather than expanded with implementation-dependent behavior.

Strings are UTF-8. Symbol names are compared using Agda's resolved identity;
the configuration reader must not normalize Unicode or rewrite operator names.
Quoted mixfix names such as `"_⟶_"` are allowed.

| Location | Requirement |
|---|---|
| `project.name` | Required nonempty display string; never selects translation behavior |
| `project.agda-library` | Required path to an existing `.agda-lib`, relative to the mapping file |
| `project.roots` | Required nonempty list of distinct Agda entry module names |
| `models` | Required nonempty mapping from unique model keys to model declarations |

Model keys are stable configuration identifiers, separate from titles and Agda
names. They consist of ASCII letters, digits, `_`, or `-`, starting with a letter.
Paths are not shell expressions. The library's include paths and dependencies
are resolved using Agda's library rules, relative to their defining files.

Entry modules determine the inspected import closure. `roots: [Example]` means
load the module `Example`; it does not mean scan every file whose module name
starts with `Example`. Every selected model module must be in that checked
closure. Additional entry modules must be listed when needed.

## Common model fields

Every model requires `module`, `state`, and `transition`. `title` and `contracts`
are optional. Omitted titles use the model key. Omitted contracts mean empty
invariant and theorem selections; they do not suppress inventory entries.

`module` names the Agda scope used to resolve unqualified references. A symbol
reference is a nonempty string naming a checked declaration. Qualified references
can address other modules in the inspected closure. Scope resolution follows
Agda visibility and export rules, including renaming and re-exports. Internal
compiler access does not grant access to a private source name from another
module.

The resolver collects canonical candidates and deduplicates paths to the same
declaration. Zero candidates produce `unresolved-symbol`; several distinct
candidates produce `ambiguous-symbol`. A unique candidate is then checked for
its requested role. No spelling convention establishes a role.

`state` is a mapping containing exactly `type`. Its value must resolve to a type
that the selected adapter can use as a complete configuration. The initial
profile requires a closed configuration type after compiler inference of
implicit arguments. Explicit project parameters requiring user-supplied
instantiation need a later profile extension and receive an
`unsupported-signature` diagnostic in version 1.

## Function encoding

The following shape selects an executable transition:

```yaml
state:
  type: World
commands:
  type: Command
transition:
  encoding: function
  symbol: step
  arguments:
    command: command
    before: w
  result:
    type: Outcome
    state-projection: outcomeWorld
    variants:
      applied: accepted
      unchanged: unchanged
      refused: refused
```

`commands` is required and contains exactly `type`. `transition` requires
exactly `encoding`, `symbol`, `arguments`, and `result`. The selected `symbol`
must resolve to a function whose body is available to the adapter. A postulated
transition has no extractable behavior.

`arguments` requires exactly `command` and `before`. Each selector is either a
source binder name or a mapping `{position: n}` selecting the zero-based explicit
argument position in the elaborated function telescope. Hidden and instance
arguments do not consume those positions. Positions count individual binders,
not groups in the printed signature. A name must identify a unique explicit
telescope binder; clause-local pattern variables do not qualify. Anonymous or
repeated binder names require positional selection.

The two roles must select distinct binders. Their types must agree with the
declared command and state types in the instantiated typing context. Other
explicit arguments remain operation inputs, with their types and dependencies
preserved; the generator must not silently assign default values. Unsupported
dependencies produce `unsupported-signature` rather than arity-based acceptance.

`result` requires `type`, `state-projection`, and `variants`. `type` identifies
the result type constructor or family. Its instantiated indices must agree with
the actual codomain. For example, naming `Outcome` does not remove a
`before` index from `Outcome before`.

`state-projection` identifies a total function with one explicit result argument
that returns the selected state type. Implicit parameters and indices must be
inferable from the transition input and result. Additional explicit projection
arguments are unsupported in this initial profile. The actual projection body
determines the after-state for every outcome.

`variants` maps each constructor of the result family to one of `accepted`,
`unchanged`, or `refused`. All family constructors must be represented exactly
once after canonical resolution; extra keys are errors. Several constructors
may share a category. Payloads and indices are retained regardless of category.
The categories choose presentation vocabulary. An `unchanged` label is not a
proof that the projected state equals the input state, and a `refused` label does
not establish the same guarantee. Unsupported or contradicted preservation
claims must not be displayed as facts.

## Relation encoding

The following shape selects an indexed relation:

```yaml
state:
  type: Configuration
transition:
  encoding: relation
  symbol: "_⟶_"
  indices:
    before: 0
    after: 1
```

`transition` requires exactly `encoding`, `symbol`, and `indices`. `commands`
and function-specific transition fields are not allowed for this profile.

The symbol must identify an inductive data family used as a relation. `indices`
requires distinct nonnegative integer `before` and `after` positions, counting
explicit indices from zero after fixed datatype parameters. Hidden indices do
not consume positions. Both selected indices must have the declared state type
in the instantiated context. Additional indices and parameters remain explicit
context in the semantic model; inability to preserve them is a diagnostic.

Each constructor supplies a transition rule. Constructor arguments, implicit
arguments, and premise evidence remain witnesses. The conclusion determines
endpoint expressions. The adapter must not treat every arrow in a constructor
signature as a runtime guard; some arguments bind values or proofs. A premise
without a decidability witness remains a proposition.

An alias to a relation may resolve to its canonical data family if the adapter
can preserve its instantiation. Arbitrary proposition-valued functions,
coinductive relations, or unsupported parameter instantiations receive an
`unsupported-encoding` or `unsupported-signature` diagnostic. Relation ordering
never selects among enabled constructors.

## Contracts

`contracts` permits `invariants` and `theorems`, each an optional list of symbol
references. Omitted lists are empty. Duplicate canonical selections are errors,
so aliases cannot silently select the same statement twice.

An invariant must resolve to a predicate over the declared state. Version 1
accepts a single explicit state argument, with inferable implicit context, and
a codomain of `Bool` or `Set`. Additional explicit context parameters require a
later selector extension and are currently unsupported. The presentation retains
the difference between a Boolean predicate and a proposition.

A theorem selection identifies a declaration whose full type is presented as
a statement. Selection does not certify that the declaration is a domain law,
that it is safely proved, or that it proves a selected invariant. The adapter
must report its declaration kind and checking assumptions. A postulate selected
here is presented as an assumption. An ordinary helper selected here must not
be promoted into a stronger statement than its actual type.

Proof dependencies and statement references are separate relationships. A proof
using a lemma and a theorem statement mentioning an operation do not have the
same meaning. All binders, premises, and conclusions survive presentation even
when the default view hides the proof body.

## Validation order and diagnostics

Validation first checks document structure, then loads and checks the Agda
input, then resolves model references, then checks role compatibility and
adapter support. Within a stage, independent errors may be collected. If an
earlier dependency fails, downstream checks must be marked blocked rather than
inventing additional type errors. Diagnostics are ordered deterministically by
mapping location, then source location and code.

| Code | Meaning |
|---|---|
| `invalid-mapping` | Syntax, key, scalar, duplicate selection, or required-field violation |
| `unsupported-mapping-version` | The configuration version has no reader |
| `agda-check-failed` | Input could not be checked using the declared environment |
| `module-outside-scope` | A selected module is outside the inspected import closure |
| `unresolved-symbol` | No canonical candidate exists in scope |
| `ambiguous-symbol` | Several canonical candidates remain |
| `invalid-selector` | A binder or index cannot be uniquely selected |
| `incompatible-role` | A resolved declaration has a demonstrably wrong type or kind |
| `unsupported-signature` | The adapter cannot yet preserve the resolved signature |
| `unsupported-encoding` | No supported encoding interpretation applies |

Unsupported extraction after a valid mapping follows the project's strict or
diagnostic generation policy. Mode selection is a generation option, not a way
to suppress mapping errors.

The [formal mapping core](../spec/Agda2SysML/Mapping.agda) accepts a role only
when a unique candidate has compatibility evidence. Its `Fits` relation and
decision procedure are parameters to be implemented by the compiler adapter.
This formal validator applies once adapter support is established. An inability
to interpret a signature is an unsupported case, not a refutation of its type
compatibility.
The core does not implement YAML parsing, Agda scoping, binder selection, or
dependent signature checking; those remain explicit implementation obligations.

## Evolution

Version 1 does not support embedded expressions, scripts, arbitrary plugin code,
guard overrides, effect overrides, or constructor renaming that changes Agda
identity. New semantic fields require a mapping version or an explicitly
versioned profile extension. A reader must never silently ignore them.

The initial format keeps display titles with model roles. Detailed layout,
styling, and prose annotations can be specified independently without changing
the meaning of a validated mapping.
