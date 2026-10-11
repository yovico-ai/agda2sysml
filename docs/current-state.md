# Current implementation checkpoint

This is an alpha development snapshot, measured on 2026-10-10 against compiler
commit `8204236`. It is useful for inspecting and
translating supported Agda domain types, calculations, and constraints. It is
incomplete. The typed S-expression core discussed as a possible next architecture
has not been implemented.

**Both generated models passed pinned Pilot validation.** The full self
translation remains incomplete: the CLI exited 2 and retained its diagnostic
bundle, with 174 unresolved requirements. The small register workflow completed
with exit 0. Validation does not imply complete translation or universal execution.

## Generated models

- [Self-specification model, gzip archive](examples/self.sysml.gz): the complete default selection
  from `spec/agda2sysml-spec.agda-lib`, root `Agda2SysML`, with partial native
  translation and explicit unresolved requirements.
- [Register workflow model](examples/register-workflow.sysml): a small complete
  mapped scope from `contracts/register-workflow.yaml`.
- [Machine-readable evidence and uncovered declarations](current-state.json):
  source/compiler identity, model hashes, coverage, validation outcomes, and
  exact declaration identifiers and remaining reasons.

The archive is about 500 KB and expands to the original 16.6 MB `.sysml` file.
From the repository root, extract it with:

```sh
gzip -dc docs/examples/self.sysml.gz > /tmp/agda2sysml-self.sysml
```

The evidence records both archive and uncompressed model hashes. These are
separate models, each defining `AgdaModel`. Load one at a time in a
fresh SysML environment. The register model is the smaller interactive example. Use the
[walkthrough](alpha.md) to regenerate full bundles including `review.html`,
source inventory, correspondence, diagnostics, and manifest. The checked-in
model files alone do not contain that complete browser/source bundle. The full
correspondence report is generated locally and is not committed to Git.

### File sizes

These are measurements for this snapshot, rounded using decimal units
(1 MB = 1,000,000 bytes). Other inputs or compiler versions can produce
different sizes.

| File | Approximate size | Availability |
| --- | ---: | --- |
| `self.sysml.gz` | 0.51 MB | Compressed download in this repository |
| `self.sysml` / self bundle's `model.sysml` | 16.6 MB | After decompression or generation |
| `register-workflow.sysml` | 11.6 KB | Plain SysML download in this repository |
| Self `inventory.json` | 38.2 MB | Generated locally |
| Self `correspondence.json` | 600.3 MB | Generated locally; excluded from Git |
| Self `review.html` | 4.3 MB | Generated locally; offline browser explorer |
| Self `diagnostics.json` / `manifest.json` | 0.53 MB / 0.38 MB | Generated locally |
| `current-state.json` | About 0.22 MB | Compact coverage and verification evidence in this repository |

The sizes above were measured in the completed self bundle.
Allow additional disk space and memory for generation and Pilot;
compressed download size does not represent their working-memory requirements.

## Coverage and its limits

| Measure | Current result |
| --- | ---: |
| Project function declarations in the checked self inventory | 722 |
| Functions with native calculations | 423 (58.6%) |
| Functions with native equality statement constraints | 247 |
| Functions represented both ways | 27 |
| Functions with either native representation | **643/722 (89.1%)** |
| Functions with neither representation | **79** |
| Unresolved requirements | **174**: 118 behavior, 56 structure |
| Discharged / required obligations | 4,352 / 4,526 |
| Native / textual equality statements | 247 / 35 |

The denominator counts original project function declarations, including Agda's
generated and module-copied functions. It excludes extra specializations from
the denominator. Native calculation coverage requires a discharged behavior
obligation with a target; statement coverage requires a translated native
statement. A declaration is counted once in their union. Retaining source or
proof text earns no native coverage. The evidence lists all 79 uncovered
canonical declarations, including distinct declarations sharing a display name.

The 174 requirements also include structures, imported dependencies, and
specialized instances, so they are not 174 distinct missing source functions.
A native fragment does not establish that every role of its declaration is
complete. Neither percentage measures application behavior covered, correctness,
work remaining, or compatibility with arbitrary Agda libraries.
These are compiler-admission counts. The assembled model passed Pilot validation
as a separate check; the 89.1% figure does not establish semantic equivalence
or completeness.

## Implemented since the original alpha

The branch extends native translation to ordered structured indices, checked
schema concatenation and map/filter calculations, natural-index arithmetic,
tagged sums, dependent records, symbolic universe levels, and native equality
statements. It supports admitted callbacks with multiple and dependent inputs,
callable record fields, captured lambdas, partial static applications, and
interleaved static/runtime parameters. Stored type and family schemas retain
membership evidence; supported recursive data cycles and empty carriers have
explicit validity constraints.

Recent changes preserve caller/callee binder scopes, resolve module copies
through checked identities, retain constructor captures, reduce checked index
helpers and record projections, and compare redundant type annotations without
changing stored values. Binding evidence retains intermediate callback-domain
types even when canonical specialization identities omit redundant annotations.
These are language-construct rules, not source-name
rules for this specification. The [rule catalogue](translation-rules.md)
describes the applicability and refusal conditions.

Agda state machines can be described through state/command types, transition
calculations, constraints, and YAML role links. Automatic SysML `state def`
synthesis and state-transition diagrams remain unimplemented.

## Remaining problems

The following are overlapping problem classes, not a partition of the 79
uncovered declarations or an estimate of how many independent fixes are needed.

| Problem | Current evidence and consequence |
| --- | --- |
| Equivalent dependent expressions receive different representations | Five `DependentRecords.ProjectedInput.Input` laws reach index-domain mismatches where separately captured callbacks and their composition have different carrier layouts. Structural similarity alone cannot safely equate those carriers. |
| Static families and runtime schema values are distinct | Several `Terms` reindexing/shape laws still pass a static family where the current representation expects a stored schema. Supporting either form independently does not establish their interchangeability. |
| Normalization is incomplete across translation boundaries | Remaining field/admission preservation laws encounter helper projections or dependent carrier expressions that the comparison rules cannot establish as equivalent. A valid Agda equality is not automatically recognized by the current target rules. |
| Dependent callbacks and impossible branches | Some refusal contracts and evidence-producing helpers cannot establish a supported callback telescope or an empty index fibre. The compiler refuses these branches rather than manufacturing an inhabitant or dropping evidence. |
| Recursive and higher-order carrier admission | Callable recursion, missing usable positivity evidence, and dependencies on unadmitted components still block some carriers and their callers. Diagnostics describe missing evidence available to the translator, not necessarily an error in the Agda source. |
| Projection and generated-helper context | Some projections require receiver refinement; generated or copied helpers can lack a unique source anchor. Reports retain per-rule failure causes, including failures of fallback rules. |
| Source correspondence remains partial | Source catalogs and derivation links exist, but transformed elaboration, generated nodes, and specialized signatures do not all have exact source-expression histories. Native semantic admission and source-derived occurrence coverage are separate. |
| Generation and artifact size | The full self model is 16.6 MB and its correspondence report is about 600 MB. This checkpoint spent 15 minutes 8 seconds generating and checking the source-linked output before Pilot started. This is an observed local run, not a performance guarantee. Large provenance output is a practical usability problem; the checked-in examples include the models and compact evidence instead of the full report. |

The CLI currently always generates the detailed correspondence report and emits
one model and one report per selected scope. It has no option to omit detailed
tracing or split these artifacts by module. This behavior belongs to the
application; the compact checkpoint evidence is a separate publication summary.

The two source-alignment laws `ambiguous-is-unavailable` and
`exact-requires-evidence`, for example, passed the latest annotation-comparison
boundary but still lack an admitted carrier. They are still counted as
uncovered. Earlier failure messages alone must not be mistaken for current
complete-operation results.

Some recorded diagnostic chains also contain missing-declaration and
unanchored-source failures. These require investigation in the translator;
they do not establish that the original Agda specification is invalid.

Architecturally, checked terms are retained in a shared JSON inventory;
`Specialize` has its own type/index expression representation, and the target
modules have carrier and expression representations. Normalization, substitution,
capture handling, and representation choices are distributed across those
layers. This makes related boundary failures recur and makes extensions costly
to assess. A unified typed core with explicit pass invariants is a possible
follow-up; merely changing serialization to S-expressions would not resolve
these semantic obligations. This checkpoint preserves the current architecture.

## Verification

All eight compiler suites passed for the callback-binding repair, including the
default Pilot checks. Two renamed fixtures exercise composed callbacks whose
intermediate type occurs only in checked index annotations; the missing-binding
assertion fails before the repair. Canonical specialization identities remain
independent of redundant annotations. The compiled source hashes match the
current implementation and regression sources. Cabal's final summary-log write
failed under the read-only cache restriction after the test suites completed;
the recorded suite results distinguish that bookkeeping failure from tests.

The repaired full model also passed independent parsed-model checks covering
11 contextual-index operations and four laws: 98 comparisons, 19 rejected
invalid cases, and 15 detected mutations. Its admitted declaration sets and
specialization identities are unchanged. Of 1,735 parsed calculations, 1,724
are unchanged; the remaining 11 carry the restored bindings, values, or related
membership constraints. The preceding annotation-comparison change is recorded
separately in the evidence.

The publication checkpoint ran the real CLI on the self aggregate and register
mapping, including source-correspondence consistency and pinned Pilot validation.
The register workflow completed with exit 0; two native field-projection
evaluations and its browser-review checks passed. The self run passed target
validation and completed with exit 2, producing its partial bundle and browser
review. Pilot took **2,108.2 seconds (35 minutes 8 seconds)**; the entire command
took **3,041.4 seconds (50 minutes 41 seconds)**. All manifest artifact hashes,
the compressed model's exact round trip, and browser-review checks passed.
Exact artifact hashes and diagnostics are recorded in the evidence file.
The whole integration suite and a fresh
non-Nix dependency installation are not claimed by this checkpoint.

The initial full-model run found four unresolved intermediate callback-type
references in specialized constructors. The generic binding-evidence repair
fixed those references and their related constraints; the successful full run
above includes that repair. The evidence retains the failed attempt separately.
Generation preceded the repair commit, so raw manifests retain the observed
earlier revision and dirty state. Source and compiled-module hashes identify
the implementation subsequently committed as `8204236`.

The measurements use a shared Linux server with an AMD Ryzen 7 5700U
(eight cores, 16 threads, frequency boost disabled) and 59.7 GiB usable RAM.
The full self-model validator uses OpenJDK 21
with a 12 GiB maximum heap. See the [runtime estimates](../validator/README.md#runtime-estimates)
for timing scope and hardware details.

Pilot acceptance establishes target parsing, name resolution, and the checks
implemented by that validator. It does not establish Agda/SysML equivalence or
successful execution of every calculation. Pilot 0.58.0 has known execution
limitations with callback bindings, invocation-dependent record construction,
constructed-value equality, type-extent quantification, and large integers.
The [interactive guide](interactive-sysml.md#execution-limits) explains these
boundaries. Independent parsed-model behavior checks are separate evidence.

No private project inputs or generated private models are included. This
checkpoint does not create a release or claim beta readiness.
