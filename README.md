# agda2sysml

**Alpha — work in progress. Already useful, with explicit limits.**

agda2sysml generates SysML 2 models from checked Agda specifications. It helps
you inspect domain types, calculations, constraints, and formal contracts,
with links back to the Agda source. It is a standalone Haskell application;
Agda supplies the behavior.

You can generate directly from an Agda library and entry module. An optional
YAML mapping identifies local modeling roles, such as state, commands, and
transitions. Unsupported constructs remain visible as incomplete requirements.

The translator targets independent Agda projects through general rules for
checked language constructs. Its own specification supplies a reproducible
walkthrough and regression corpus. Compatibility with another project depends
on the supported constructs and their composition; self-specification coverage
alone does not establish that compatibility.

Start with the [alpha walkthrough](docs/alpha.md). It explains how to run the
generator on **its own Agda specification**, what output to expect, and how to
explore it. The [interactive SysML guide](docs/interactive-sysml.md) covers the
browser review and the official SysML notebook tools.

The [current implementation checkpoint](docs/current-state.md) records coverage,
remaining problems, verification results, and downloadable generated models.
The original alpha release and the current development snapshot have different
capabilities; the checkpoint identifies the measured implementation.

## Implemented functionality

- Check an Agda library and its entry modules; inventory the checked import
  closure with types, definitions, source text, dependencies, and assumptions.
- Generate native SysML for supported enumerations, records, constructor
  payloads, Boolean and finite-domain calculations, first-order helper calls,
  finite natural arithmetic, and ordered lists.
- Retain supported dependent indices, type parameters, indexed family
  parameters, concrete and symbolic static universe levels, and safe inductive
  recursive carriers. Checked recursive calculations preserve their inputs.
  Natural-sum indices support vector concatenation, captured/runtime slot
  injection, and shifting bounded spans with their complete order evidence.
- Specialize supported concrete higher-order calls and perform checked
  definitional reduction at generation time.
- Translate supported unary and multiargument callback inputs, including indexed and dependent
  signatures, as native SysML
  calculations, including invocation and forwarding through recursive helpers.
  Store these callbacks in records and constructor payloads: supplied decision
  trees and ordered rule lists can retain guards, complete outcomes, and fallback
  behavior through `evaluate`, `evaluatePartial`, `select`, and `withFallback`.
  Supported lambdas retain their captured values and callbacks: `restrict`
  constructs combined guards, and `normalize` converts decision trees to ordered
  rules while preserving complete outcomes.
  `AlgebraicValues.tabulate` also constructs complete fields from an indexed
  callback, preserving distinct positions even when field types repeat.
  The self specification's first-order evaluator also translates table lookup,
  expression evaluation, argument lists, and evidence-producing operation members.
  Supplied calculations can compute dependent record and constructor indices;
  input and result constraints check the selected membership while retaining
  complete payloads and equality evidence.
  Supported signatures can interleave runtime inputs with type and universe
  parameters, including a later callback result type. Dependent sum dispatch
  passes the complete tag and payload to the supplied calculation.
  Callback behavior is independently tested; the pinned Pilot cannot execute
  the callback bindings reliably.
- Translate supported indexed validation procedures with their complete evidence.
  The self model classifies reports, accepts only fully translated reports, and
  validates mapping candidates, distinguishing missing, ambiguous, and incompatible
  choices. Constructor and list patterns retain their dependent input contracts.
- Translate supported typed collection conversions that filter static slots,
  preserve dynamic payloads, and adjust positions. Checked map/filter helpers can
  compute dependent indices, including callback-based member conversion.
- Retain supported type and indexed-family fields in records as runtime schema
  bindings. Conversion, selection, and reindexing preserve complete domain
  values and membership evidence, with constraints linking them to their binding.
  Index domains can depend on earlier record fields. Supported nonrecursive
  record families construct bindings using native collection expressions and
  the supplied domain extents, preserving witnesses and evidence.
- Describe **state machines** using Agda state/command types and transition
  functions or supported finite relations. YAML roles connect the state,
  commands, transition, outcomes, and selected contracts in the correspondence
  report. The alpha emits their native types, calculations, and constraints;
  automatic SysML `state def` synthesis and state-transition diagrams are
  future work.
- Emit supported equality theorem statements as native SysML constraints,
  retaining their inputs, hypotheses, index contracts, and proof-source links.
  Unsupported statements and proof bodies remain inspectable source contracts;
  native statements and executable calculations have separate coverage counts.
- Write validated SysML, completeness diagnostics, source correspondence,
  artifact hashes, and a self-contained `review.html` with search and filters.

The [translation rules](docs/translation-rules.md) define each capability's
applicability boundary. Features compose only when their checked dependencies
also have supported representations.

## Quick start: this project's specification

Install the application and pinned validator using the
[build instructions](docs/installation.md). Nix is an optional reproducible
build environment; generation itself is a Haskell application invoking Java.
With the installed executables on `PATH`, run from this checkout:

```sh
AGDA2SYSML_LIBRARIES_FILE=/dev/null agda2sysml generate \
  --library spec/agda2sysml-spec.agda-lib \
  --root Agda2SysML \
  --diagnostic \
  --output /tmp/agda2sysml-alpha-self
```

On Unix, `/dev/null` supplies an empty Agda dependency registry for this builtin-only
specification. Use an output directory that does not already exist.
The self specification still contains unsupported constructs. A partial
translation whose model passes validation exits **2** and retains its diagnostic
bundle. See the [checkpoint results](docs/current-state.md) for measured coverage
and validation evidence.
Exit 0 means the requested scope is complete; exit 1 means configuration,
checking, validation, or I/O failed.

Explore a generated bundle through `review.html`. For a small, complete
state-update model, run:

```sh
AGDA2SYSML_LIBRARIES_FILE=/dev/null agda2sysml generate \
  --mapping contracts/register-workflow.yaml \
  --output /tmp/agda2sysml-alpha-register
```

This mapped example exits 0; open `/tmp/agda2sysml-alpha-register/review.html`
in a browser. See the
[full walkthrough](docs/alpha.md) for commands, expected artifacts, and examples
of native and untranslated self-specification declarations.

## Alpha limitations

The alpha is useful for model inspection and for supported executable
fragments. It does **not** translate arbitrary Agda completely. Unsolved universe
constraints, arbitrary higher-order values, unsupported recursive families, general
dependent computation, and parts of source correspondence remain unfinished.
The output format and translation coverage may evolve.

The default self model has 423 native calculation functions out of 722 (58.6%)
and 247 native equality statements, including compiler-generated or module-copied helpers.
Twenty-seven functions have both representations: 643/722 function declarations (89.1%)
have a native calculation or statement constraint. This is declaration
coverage, not a percentage of application behavior or a correctness claim.
There are still 174 unresolved requirements. Source-only proof retention is
excluded from native coverage.
See the [checkpoint](docs/current-state.md) for the exact uncovered declarations
and the distinction between declaration coverage, requirement completion, and
Pilot validation.

SysML validation checks parsing, names, and types. It does not prove
equivalence or guarantee that a downstream tool can execute every calculation.
The pinned Pilot evaluator has limits with returned record construction,
type-extent quantification, and large-integer arithmetic. The guide explains
which interactive examples work and how to recognize unevaluated results.

## Development and evidence

```sh
nix develop
cabal build all
cabal test all --test-options=--compiler-only --test-show-details=direct
nix flake check --print-build-logs
```

The compiler-only test command runs all eight Haskell suites without starting
Pilot. The default test options and the full flake checks still include Pilot.

CI checks the safe Agda aggregate, eight Haskell suites, native SysML validation,
CLI behavior, reproducibility, the browser review, and independent comparisons
of parsed emitted calculations. The recursive compiler core alone has 24,542
result comparisons, ten invalid-case checks, and a constraint-removal mutation.

- [Project specification](SPECIFICATION.md)
- [Project mapping format](docs/project-mapping.md) and [version 2](docs/project-mapping-v2.md)
- [CLI and artifact contract](docs/cli.md)
- [Formal laws](spec/README.md) and [correspondence boundaries](docs/correspondence.md)
- [Historical acceptance inventory](docs/acceptance-inventory.md)

Generation is local and performs no publication or upload.

## License

MIT. See [LICENSE](LICENSE). The separate upstream SysML tools retain their own
licenses; see [validator information](validator/README.md).
