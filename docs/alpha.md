# Alpha walkthrough

agda2sysml is a **work in progress that is already useful, but limited**. It
generates SysML 2 types, calculations, and constraints for supported Agda
constructs, and keeps unsupported definitions visible with their checked source
and an explanation. This guide uses the project's own formal specification and
its independent public state-update contracts.

The generator is generic. YAML supplies local modeling roles; it does not
provide project-specific executable code or replace Agda behavior. The
[README](../README.md#implemented-functionality) lists implemented features,
and the [translation rules](translation-rules.md) state their exact boundaries.

## 1. Get and build the alpha

You need Git and Nix with the `nix-command` and `flakes` experimental features
enabled. The flake supplies pinned Agda 2.8.0, GHC, Cabal, Java, and the SysML
validator. You do not need a separately installed Agda standard library for
this project's builtin-only specification.

```sh
git clone https://github.com/yovico-ai/agda2sysml.git
cd agda2sysml
nix build
./result/bin/agda2sysml --version
./result/bin/agda2sysml --help
```

For the release snapshot, check out `v0.1.0-alpha.1` before building. The CLI
reports `agda2sysml 0.1.0 (Agda 2.8.0)`; the release's alpha status describes
its maturity. This is a source release: Nix builds the application locally.
The first build can download or compile substantial dependencies and run the
package's tests. Subsequent builds reuse the Nix store.

Verification for this alpha was performed on x86_64 Linux. The flake also
declares other platforms; that is not evidence that this release was checked
on all of them.

If you prefer a development build, from the repository root run:

```sh
nix develop --command cabal build all
nix develop --command cabal run agda2sysml -- --help
```

You can substitute `nix develop --command cabal run agda2sysml --` for
`nix develop --command ./result/bin/agda2sysml` in the self-specification and
public-contract commands below.

## 2. Generate from the project's own Agda files

From the repository root:

```sh
nix develop --command ./result/bin/agda2sysml generate \
  --library spec/agda2sysml-spec.agda-lib \
  --root Agda2SysML \
  --diagnostic \
  --output /tmp/agda2sysml-alpha-self
```

The output directory **must not already exist**. For another run, choose a new
directory, such as `/tmp/agda2sysml-alpha-self-next`. The generator does not
edit the input Agda files.

The library descriptor selects `spec/`; the entry module imports the formal
modules. The generator checks that import closure and selects every declaration
owned by this library. It follows required dependencies into imported libraries.
An unimported Agda file is outside this invocation's scope. No YAML is needed.
The Nix shell supplies an empty installed-library registry for these builtin-only
inputs. Invoking the packaged CLI outside that shell uses your normal Agda
registry, which must contain valid library paths even if this input needs no
additional libraries.

**Expect exit status 2.** The full self-specification is currently incomplete
as a native translation. `--diagnostic` requests a usable partial bundle,
including a model accepted by the pinned SysML validator. Exit 2 here is the
documented result, not a failed Agda compilation. If running under `set -e` or
in automation, handle it explicitly:

```sh
if nix develop --command ./result/bin/agda2sysml generate \
    --library spec/agda2sysml-spec.agda-lib \
    --root Agda2SysML --diagnostic \
    --output /tmp/agda2sysml-alpha-self-next; then
  echo "Complete translation"
else
  generation_status=$?
  if [ "$generation_status" -eq 2 ]; then
    echo "Partial translation: inspect the diagnostic bundle"
  else
    echo "Generation failed with status $generation_status" >&2
    exit "$generation_status"
  fi
fi
```

| Status | Meaning |
| --- | --- |
| `0` | The requested operation completed; generation's required scope is complete and validated. |
| `2` | Translation requirements remain unresolved. Diagnostic mode retains the partial model. |
| `1` | Configuration, Agda checking, target validation, or I/O failed. |

An incomplete bundle must never be treated as strict success. The current
alpha also retains an explicitly incomplete bundle when `--diagnostic` is
omitted; its status remains 2 and `complete` remains false. Use `--diagnostic`
to make your intent to explore partial results clear, and always check status
and completeness in automation.

## 3. Read the result

The generation directory contains:

| File | Use |
| --- | --- |
| `review.html` | Self-contained browser exploration of declarations, source, native fragments, and missing requirements. |
| `model.sysml` | The generated SysML 2 textual model, rooted at package `AgdaModel`. |
| `correspondence.json` | Required scope, native targets, retained contracts, unresolved obligations, modeling roles, and source correspondence. |
| `inventory.json` | Checked declarations, source documents, types, dependencies, compiler terms, and checking assumptions. |
| `diagnostics.json` | Reasons for unresolved translation requirements or failures. |
| `manifest.json` | Toolchain and input identities, artifact hashes, scope, validation result, and completeness. |

The alpha self-model snapshot has `complete: false`,
`targetValidation: "accepted"`, 74 native project functions, and 740 unresolved
requirements. The counts can change with the specification or entry modules;
they are not a percentage of implementation completion. Source/proof retention
is accounted for separately from executable translation.

For a quick summary, from the repository root:

```sh
nix develop --command python3 - <<'PY'
import json
from pathlib import Path
bundle = Path('/tmp/agda2sysml-alpha-self')
manifest = json.loads((bundle / 'manifest.json').read_text())
report = json.loads((bundle / 'correspondence.json').read_text())
print('Complete:', manifest['complete'])
print('Target validation:', manifest['targetValidation'])
print('Coverage:', report['coverage'])
for item in report['obligations']:
    if item['status'] == 'textual':
        print(item['symbol'], item['kind'], item['reason'])
        break
PY
```

The final line shows one unresolved requirement; the JSON and browser list the
others. A translated declaration can have additional unresolved requirements,
so a native fragment alone does not establish completeness of its whole scope.

## 4. Explore the self-model in a browser

Open `/tmp/agda2sysml-alpha-self/review.html` using your browser's **Open File**
command. Keep the bundle together: its links open sibling artifacts. The review
uses embedded data and needs no web server or network access.

1. Filter by a module, such as `Agda2SysML.BooleanLowering`.
2. Select **Has native SysML** and search for `lower` or `lookup`.
3. Select a declaration to compare its checked Agda source with its native
   calculations and constraints. The core `Fin`, `Vec`, `Cases`, `Expr`,
   `lookup`, `remove`, `source`, `target`, and `lower` are implemented.
4. Explore `Resolution.resolve`, `Foundation.orElse`, and `Foundation._++_`
   for generic resolution, fallback, and list concatenation.
5. Choose **Retained proof contracts** and inspect
   `BooleanLowering.lower-preserves`. Its source law is retained; this label
   does not claim that SysML executes the proof.
6. Choose **Needs translation** to inspect the remaining boundaries and their
   diagnostics. Open the correspondence or inventory links for full details.

The browser is a read-only source/model explorer, not a graphical SysML editor
or simulator. For model inspection, diagrams, and supported calculation
evaluation in a SysML environment, follow the
[interactive guide](interactive-sysml.md).

## 5. Describe and inspect a state machine

Agda can describe a state machine with a state type, command constructors, a
transition function, and preservation laws. The public `Register` contract
defines a state with Boolean `value` and `enabled` fields. Commands retain,
write, enable, or replace that state. `RegisterWorkflow.sequence` composes two
updates while retaining the complete intermediate state.

Generate its deliberately selected, complete model:

```sh
nix develop --command ./result/bin/agda2sysml generate \
  --mapping contracts/register-workflow.yaml \
  --output /tmp/agda2sysml-alpha-register
```

Expect exit 0, `complete: true`, and accepted target validation. In
`model.sysml`, inspect `Register.State`, `Register.Command`, `Register.step`,
and `RegisterWorkflow.sequence`. Their native types and calculations describe
the state and its updates. The mapped model has linked transition targets in
`correspondence.json` under `models.sequential`.

The YAML selects the existing Agda roles; it supplies no replacement guard,
effect, or command implementation. Additional operation inputs remain explicit
context. Invariants and theorems are linked as contracts. Supported finite
relations can also describe permitted before/after states.

**State-machine semantics are implemented through types, calculations,
constraints, and mapping links. Automatic native SysML `state def` generation
and state-transition diagrams are not implemented.** A tree diagram of the
generated types is not a state-transition diagram.

Mapping-only generation selects a scope. Adding `--mapping` to automatic
`--library`/`--root` generation instead adds local roles to the whole selected
declaration scope; it cannot hide unsupported ordinary calculations. See the
[mapping formats](project-mapping.md) and [CLI contract](cli.md).

## 6. Use your own library

Use the same command form with your `.agda-lib` and entry module:

```sh
./result/bin/agda2sysml generate \
  --library /absolute/path/to/project/project.agda-lib \
  --root Project \
  --diagnostic \
  --output /tmp/project-sysml
```

Repeat `--root` for distinct entry modules. Keep the declared library
dependencies available through Agda's installed-library registry. If necessary,
set `AGDA2SYSML_LIBRARIES_FILE` to your registry file; the Nix development shell
uses an empty registry for the builtin-only self-specification. This variable
names a registry containing paths to `.agda-lib` files, not a source directory.
Agda dependency libraries and the registry must be compatible with the pinned
compiler. `inspect` checks and inventories input without generating SysML.

Start with a small meaningful import closure and inspect its diagnostics before
expanding to a large library. The alpha supports useful fragments rather than
every dependent or higher-order Agda program.

## Verification and current limits

From the repository root, run the same check as CI:

```sh
nix flake check --print-build-logs
```

It checks the safe formal aggregate, eight Haskell suites, native validation,
CLI artifacts and reproducibility, mapping refusals, browser behavior, and
independent comparisons of parsed emitted SysML. The recursive core contributes
24,542 result comparisons, including unequal source/target contexts, ten
invalid-case rejections, and a removed-constraint mutation.

Open universe levels, arbitrary higher-order values, unsupported recursive
families, general dependent computation, and some source correspondence remain
unfinished. The formal laws are general, but they do not constitute an
end-to-end proof of the Haskell adapter or renderer. SysML validation and actual
downstream execution are different checks; see the interactive guide for the
pinned evaluator's limits.

Changes belong in the Agda specification or local mapping, followed by fresh
generation into a new directory. Generated SysML is not a reverse translator
into Agda. You can experiment in a separate SysML notebook or copy while
keeping the generated bundle and its hashes intact.
