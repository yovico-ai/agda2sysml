# Working with generated SysML interactively

There are two complementary workflows: the generated browser review for
source-aware exploration, and a SysML environment for inspecting declarations,
visualizing model elements, and evaluating supported calculations. Both use the
same `model.sysml`; validation does not imply universal execution support.

## Browser review: no additional installation

Generate the self-model as described in the [alpha walkthrough](alpha.md), then
open `/tmp/agda2sysml-alpha-self/review.html` in a browser.

Search by name, checked source, or diagnostic text. Filter by module and by
**Has native SysML**, **Retained proof contracts**, or **Needs translation**.
Selecting a declaration displays its checked source, native fragments, and
requirements. Links open the full SysML, correspondence report, and inventory.
The page works offline and requires no server.

This is a read-only explorer. It does not edit the model, draw state-transition
diagrams, or execute calculations.

## Official SysML notebook environment

The alpha's validator uses the official SysML Pilot release **2026-03**, Jupyter
SysML kernel **0.58.0**, and its matching standard libraries. Use that version
for the reproducible examples below. Other tool versions may differ.

The following setup follows the upstream
[kernel installation instructions](https://github.com/Systems-Modeling/SysML-v2-Pilot-Implementation/blob/3a1be5b876890d9232f5757e3a7f3cb30bbd646d/org.omg.sysml.jupyter.kernel/README.adoc).
It uses a separate Python environment and the prebuilt kernel archive. You need
a full Java 21+ JDK/JRE with font support, Python 3 with `venv`/pip, `curl`,
`unzip`, and Graphviz's `dot` on your path. A headless Java package can suffice
for validation but lack the font libraries needed for diagrams. These
interactive tools are optional; the generator already includes its own
validator through Nix.

On Linux or macOS, outside the application checkout:

```sh
mkdir -p "$HOME/agda2sysml-notebooks"
cd "$HOME/agda2sysml-notebooks"
python3 -m venv .venv
. .venv/bin/activate
python -m pip install 'jupyterlab>=4,<5' 'jupyter-console>=6,<7'
curl -fL \
  https://github.com/Systems-Modeling/SysML-v2-Pilot-Implementation/releases/download/2026-03/jupyter-sysml-kernel-0.58.0.zip \
  -o sysml-kernel-0.58.0.zip
unzip sysml-kernel-0.58.0.zip -d pilot-0.58.0
python pilot-0.58.0/install.py --sys-prefix \
  --library-path "$PWD/pilot-0.58.0/sysml/sysml.library" \
  --graphviz-path "$(command -v dot)"
jupyter kernelspec list
jupyter lab
```

Check that `sysml` appears in the kernel list. The configured library path is
absolute and points to the libraries bundled with this kernel. The
[release-specific upstream installer](https://github.com/Systems-Modeling/SysML-v2-Release/blob/2026-03/install/jupyter/README.adoc)
also documents installation on Windows. For later sessions, activate this
environment and run `jupyter lab`; installation is not needed again.
On a server or a remote session without an accessible desktop display, use
`JAVA_TOOL_OPTIONS=-Djava.awt.headless=true jupyter lab`. This enables offscreen
rendering with a full Java runtime; it does not supply missing font libraries.

## Import the generated model locally

Create a notebook using the **SysML** kernel. Open the generated `model.sysml`
in a text editor, copy its complete contents into the first notebook cell,
and run that cell with **Shift+Enter**. For the self-model, use
`/tmp/agda2sysml-alpha-self/model.sysml`. The cell defines the `AgdaModel`
package. Wait for parsing and validation before running further cells.

Keep the whole file together: copied fragments can depend on generated types
or helpers declared elsewhere in the bundle. Start a fresh kernel when switching
between different generated bundles, since each defines `AgdaModel`.

**Do not use `%load /path/model.sysml` as a local-file command.** In this kernel,
`%load` accesses a model repository. Copying the textual model into a SysML cell
loads it locally without configuring or publishing to a repository.

## Inspect and visualize the self-model

Run each command in its own SysML notebook cell:

```text
%show AgdaModel::'Agda2SysML.BooleanLowering.Expr'
```

This shows the expression carrier's model structure. Generated qualified Agda
names containing dots are quoted **single SysML names**; preserve the quotes.
Use exact names from `model.sysml` or a `target` in `correspondence.json`, since
specializations and disambiguated names can contain additional suffixes.

```text
%viz --view=tree AgdaModel::'Agda2SysML.BooleanLowering.Expr'
```

This requests a structural diagram of that carrier. Start with one declaration;
rendering the whole self-model can create a large, unhelpful diagram. The
browser review is more convenient for surveying the whole declaration set.

```text
%eval --target=AgdaModel 'Agda2SysML.Foundation.not'(true)
```

Expect a `LiteralBoolean false` result, possibly with a generated element ID.
This is a small supported calculation, not a simulation of the whole model.

Useful command help is available in the same kernel:

```text
%help show
%help viz
%help eval
```

The examples above are checked using the pinned kernel's actual command parser
and generated self-model. Notebook visualization displays SVG using Graphviz.
If a diagram reports a renderer exception, check that `dot` is installed and
that the configured path points to its executable. If a reference is unresolved,
check that the entire model cell ran successfully and use its exact target name.

## Inspect theorem constraints

In a newly generated self-model, find a translated row in
`correspondence.json.nativeStatements` and use its exact `target` with `%show`.
For example:

```text
%show AgdaModel::'Agda2SysML.NaturalValues.source-roundtrip.law'
```

Its `constraint def` exposes the theorem's input and its equality conclusion.
Other laws also take explicit type/family bindings and premise witnesses. Supply
all of those when evaluating a constraint; a proof-valued input must satisfy
its complete carrier and index contracts. Read the original theorem and proof
through the corresponding source links in the review page.

A translated statement is usable as a model constraint, independently of
whether Pilot can execute its particular expression dependencies. The pinned
Pilot's execution limits below still apply. Validator acceptance and a few
successful evaluations do not establish a universally quantified proof.

## Explore the mapped state-update model

Generate the public register workflow using the command in the alpha guide.
In a **fresh kernel**, put the complete contents of
`/tmp/agda2sysml-alpha-register/model.sysml` into the first cell and run it.

Then inspect its domain and transition calculation:

```text
%show AgdaModel::'Register.State'
```

```text
%show AgdaModel::'RegisterWorkflow.sequence'
```

```text
%viz --view=tree AgdaModel::'Register.State'
```

The model describes state-machine semantics through the state and command
carriers, transition calculations, constraints, and mapping role links. The
generated file does not contain native SysML `state def` elements. Accordingly,
a tree view shows the state type, not a state-transition diagram, and requesting
a state view does not synthesize the missing diagram.

Use `correspondence.json` to follow the selected transition's inputs, complete
result state, linked contracts, and target declarations. Inspect the `step` and
`sequence` bodies to see how commands update the state. The generator does not
enumerate an arbitrary state domain into a finite graphical state graph.

## Editing and regeneration

You can edit a notebook copy or a separate `.sysml` file for model exploration.
Those edits are local SysML experiments: they are not written back to Agda and
no longer carry the original bundle's unchanged artifact hashes.

For a source change, update Agda or the YAML modeling roles, regenerate into a
new directory, and load the new model in a fresh kernel. Keep the original
bundle for comparison. A SysML editor supporting matching SysML 2 libraries can
also open `model.sysml`; editor-specific visualization and execution support
vary. The generated `review.html` remains a portable way to inspect its source
and translation boundaries.

## Execution limits

The pinned validator checks syntax, names, and types. It does not prove
equivalence to Agda or establish that a particular execution engine can run
every native calculation.

Pilot 0.58.0 can evaluate supported scalar calculations and some projection,
dispatch, and helper-call cases. It cannot reliably evaluate every returned
record construction with invocation-dependent fields, every type-extent
quantifier, or arbitrary-precision natural arithmetic. A result that remains
an expression or feature reference is **unevaluated**, not a successful value.
Evaluate small supported examples and inspect the returned result explicitly.

Pilot 0.58.0 also returns `false` in the following comparisons of equivalent
constructed attribute values. Both identical field order and reordered values
of an unordered field reproduce the limitation:

```sysml
attribute def Unordered {
  attribute values : ScalarValues::Boolean [0..*];
}
```

```text
%eval new Unordered(values=(true,false)) == new Unordered(values=(false,true))
%eval new Unordered(values=(true,false)) == new Unordered(values=(true,false))
```

Consequently, an equality law involving constructed records may evaluate to
`false` in Pilot even for equivalent values. These checks do not establish the
underlying evaluator cause. The independent
test interpreter follows the declared ordering and uniqueness of each field,
including all payloads and evidence. This follows the data-value and feature
semantics in [KerML 1.0, sections 7.4.2 and 8.4.3.4](https://www.omg.org/spec/KerML/1.0/PDF).
Native constraint validation and independent behavior checks are reported
separately from Pilot execution; the latter is not claimed for every law.

Native unary callback inputs use `in calc` and invoke the bound calculation
directly. Stored callable members use `ref calc` inside immutable attribute
definitions. The generated `DecisionTree.evaluate`, `evaluatePartial`, `select`,
and `withFallback` accept supplied trees and rule lists, including their callable
members. Inspect the constructor helpers, selected payloads, member signatures,
and recursive calculation bodies in the model. Reconstruction retains the
supplied callable references and full result values.

Pilot 0.58.0 accepts these models but may leave callback invocations
unevaluated, including forwarded bindings whose direct calculations evaluate
successfully. Inspect their signatures, bodies and contracts interactively;
do not treat an unresolved `InvocationExpression` as the callback's result.
The independent parsed-model tests cover these operations; they are not evidence
that Pilot can execute the same bindings. See the
[callback rule and limitations](translation-rules.md#native-unary-callback-inputs)
and [callable members](translation-rules.md#native-callable-members).

The project's independent tests parse emitted SysML and compare complete results
for supported algorithms, including recursive and parameterized ones. That
evidence is distinct from Pilot runtime execution. Retained Agda proofs remain
inspectable contracts; the notebook does not execute them as proofs. See
[translation rules](translation-rules.md) and
[correspondence boundaries](correspondence.md) for details.
