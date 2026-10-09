# agda2sysml

**Alpha — work in progress. Already useful, with explicit limits.**

agda2sysml generates SysML 2 models from checked Agda specifications. It helps
you inspect domain types, calculations, constraints, and formal contracts,
with links back to the Agda source. It is a standalone Haskell application;
Agda supplies the behavior.

You can generate directly from an Agda library and entry module. An optional
YAML mapping identifies local modeling roles, such as state, commands, and
transitions. Unsupported constructs remain visible as incomplete requirements.

Start with the [alpha walkthrough](docs/alpha.md). It explains how to run the
generator on **its own Agda specification**, what output to expect, and how to
explore it. The [interactive SysML guide](docs/interactive-sysml.md) covers the
browser review and the official SysML notebook tools.

## Implemented functionality

- Check an Agda library and its entry modules; inventory the checked import
  closure with types, definitions, source text, dependencies, and assumptions.
- Generate native SysML for supported enumerations, records, constructor
  payloads, Boolean and finite-domain calculations, first-order helper calls,
  finite natural arithmetic, and ordered lists.
- Retain supported dependent indices, type parameters, indexed family
  parameters, concrete type/universe specializations, and safe inductive
  recursive carriers. Checked recursive calculations preserve their inputs.
- Specialize supported concrete higher-order calls and perform checked
  definitional reduction at generation time.
- Translate supported unary, nondependent callback inputs as native SysML
  calculations, including invocation and forwarding through recursive helpers.
  Callback behavior is independently tested; the pinned Pilot validates these
  models but cannot execute the callback bindings reliably.
- Describe **state machines** using Agda state/command types and transition
  functions or supported finite relations. YAML roles connect the state,
  commands, transition, outcomes, and selected contracts in the correspondence
  report. The alpha emits their native types, calculations, and constraints;
  automatic SysML `state def` synthesis and state-transition diagrams are
  future work.
- Retain formal statements and proofs as inspectable source contracts.
  Retention is distinguished from executable translation.
- Write validated SysML, completeness diagnostics, source correspondence,
  artifact hashes, and a self-contained `review.html` with search and filters.

The [translation rules](docs/translation-rules.md) define each capability's
applicability boundary. Features compose only when their checked dependencies
also have supported representations.

## Quick start: this project's specification

Install Nix with flakes enabled and Git, then:

```sh
git clone https://github.com/yovico-ai/agda2sysml.git
cd agda2sysml
nix build
nix develop --command ./result/bin/agda2sysml generate \
  --library spec/agda2sysml-spec.agda-lib \
  --root Agda2SysML \
  --diagnostic \
  --output /tmp/agda2sysml-alpha-self
```

The Nix shell supplies an empty Agda dependency registry for this builtin-only
specification. Use an output directory that does not already exist. **Exit 2 is expected for
this example**: the whole self-specification is only partially translated.
The diagnostic bundle still contains validated SysML and identifies the
unresolved requirements. Exit 0 means the requested scope is complete; exit 1
means configuration, checking, validation, or I/O failed.

Open `/tmp/agda2sysml-alpha-self/review.html` in a browser. For a small, complete
state-update model, run:

```sh
nix develop --command ./result/bin/agda2sysml generate \
  --mapping contracts/register-workflow.yaml \
  --output /tmp/agda2sysml-alpha-register
```

This mapped example should exit 0. See the
[full walkthrough](docs/alpha.md) for commands, expected artifacts, and examples
of native and untranslated self-specification declarations.

## Alpha limitations

The alpha is useful for model inspection and for supported executable
fragments. It does **not** translate arbitrary Agda completely. Open universe
levels, arbitrary higher-order values, unsupported recursive families, general
dependent computation, and parts of source correspondence remain unfinished.
The output format and translation coverage may evolve.

The default self model currently has 74 native project functions and 740
unresolved requirements. These are coverage observations, not a completion
percentage or an end-to-end correctness claim. Formal proof contracts can be
retained even when associated ordinary calculations remain unsupported.

SysML validation checks parsing, names, and types. It does not prove
equivalence or guarantee that a downstream tool can execute every calculation.
The pinned Pilot evaluator has limits with returned record construction,
type-extent quantification, and large-integer arithmetic. The guide explains
which interactive examples work and how to recognize unevaluated results.

## Development and evidence

```sh
nix develop
cabal build all
nix flake check --print-build-logs
```

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
