# Implementation acceptance inventory

**Historical snapshot: 2026-10-07.** For the current self-specification coverage,
generated models, Pilot results, and remaining problems, see the
[current implementation checkpoint](current-state.md). The measurements below
remain evidence for their recorded implementation, not current branch results.

The native generator works for a substantial finite, first-order fragment, but
full acceptance under the [project specification](../SPECIFICATION.md#acceptance-criteria)
is not established. Remaining work includes semantic capability limits, incomplete
source correspondence, and external acceptance evidence. Passing CI establishes
the implemented fragment and its explicit refusals; it does not establish complete
translation of arbitrary Agda specifications.

This inventory records the implementation measured on 2026-10-07. The exact
implementation tree, binary digest, artifact digests, per-mapping results, and
verification metadata are in [the evidence dataset](acceptance-evidence.json).
The snapshot contains staged implementation changes; it is not a published release.

## Measured coverage

All 13 public mappings were generated in diagnostic mode with the current binary
and the pinned validator. Eleven returned 0 with `complete: true`; two returned 2
with `complete: false`. All 13 emitted models were accepted by the validator,
including the explicitly incomplete diagnostic models. Source catalogs, checked
references, derivation links, target intervals, and manifest artifact digests
were validated for every bundle.

| Measure | Result | Interpretation |
|---|---:|---|
| Complete public mappings | 11/13, **84.6%** | These mapped scopes satisfied the semantic completion criteria |
| Source-derived target occurrences | 612/2,271, **26.9%** | Marked emitted occurrences with validated source derivation chains |
| Source-derived calculations | 38/207, **18.4%** | Whole marked calculations whose required origin histories are ready |
| Discharged behavior obligations | 159/163 | Counted across all bundles, including repeated imported definitions |
| Discharged structure obligations | 306/320 | Same repeated-bundle accounting |
| Retained statement obligations | 404/404 | Exact statement retention, not executable translation |
| Retained proof-source obligations | 387/387 | Proof-source retention, not a proof of the generator |

The combined obligation count is 1,256/1,274. Its high ratio includes 791
statement/proof-source obligations and must not be presented as a percentage of
executable semantics implemented. Likewise, 84.6% of these mappings is not 84.6%
of project work. The mappings are maintained public contracts, not a representative
sample of all Agda programs or an external project's full corpus. Occurrence
counts repeat imported code between bundles and count renderer marks rather than
all SysML syntax nodes or source lines. Incomplete mappings with no emitted
occurrences have no provenance denominator. No workload completion percentage
is established by these measurements.

| Public mapping | Semantic status | Discharged obligations | Source-derived target occurrences |
|---|---|---:|---:|
| [computed-index](../contracts/computed-index.yaml) | Complete | 146/146 | 59/234 |
| [dependent-payload](../contracts/dependent-payload.yaml) | Complete | 207/207 | 250/734 |
| [dependent-record](../contracts/dependent-record.yaml) | Complete | 111/111 | 103/222 |
| [guarded](../contracts/guarded.yaml) | Incomplete | 41/53 | No emitted occurrences |
| [implication](../contracts/implication.yaml) | Complete | 23/23 | 10/12 |
| [indexed](../contracts/indexed.yaml) | Complete | 99/99 | 63/180 |
| [parameterized](../contracts/parameterized.yaml) | Complete | 110/110 | 2/151 |
| [register-workflow](../contracts/register-workflow.yaml) | Complete | 56/56 | 46/93 |
| [register](../contracts/register.yaml) | Complete | 58/58 | 40/95 |
| [relational](../contracts/relational.yaml) | Incomplete | 13/19 | No emitted occurrences |
| [specialized-indexed](../contracts/specialized-indexed.yaml) | Complete | 233/233 | 12/435 |
| [universe-polymorphic](../contracts/universe-polymorphic.yaml) | Complete | 118/118 | 12/97 |
| [witnessed](../contracts/witnessed.yaml) | Complete | 41/41 | 15/18 |

`Guarded` has 12 unresolved obligations: open universe/carrier requirements,
parameterized command and outcome structure, and the transition/projection/
generated helper bodies. `Relational` has 6: open universe requirements and its
parameterized relation family and constructors. Both are checked and inventoried;
the generator correctly refuses to label their behavior completely translated.
The exact symbols, categories, and explanations are retained in the dataset.

## Acceptance criteria and evidence

“Demonstrated” below is limited to the reviewed implementation and public checks.
It does not assert correctness of every input accepted by the compiler adapter.
The seven criteria retain their meaning from the specification.

| Criterion | Status | Evidence and remaining condition |
|---|---|---|
| Independently authored projects using both encodings map without project-specific branches | Partial | Both profiles are implemented and public finite function/relation contracts translate. General `Guarded` and `Relational` remain incomplete. Establish acceptance on independently authored projects with an explicit required scope; the maintained public suite alone does not establish independent authorship. See [contracts](../contracts/README.md), [Compiler](../src/Agda2SysML/Compiler.hs), and [RelationTarget](../src/Agda2SysML/RelationTarget.hs). |
| Missing, ambiguous, incompatible, and dependent role references are handled without guessing | Demonstrated for supported profiles | [Mapping](../src/Agda2SysML/Mapping.hs), `Compiler.validateModel`, [mapping tests](../test/MappingTests.hs), and [CLI tests](../test/integration.py) cover parsing, resolution, selectors, conversion, and refusals. Unsupported signatures remain explicit. |
| Commands, payloads, conditions, effects, refusal precedence, and relation alternatives have exact source correspondence | Partial | Native lowering covers the admitted fragment. Source correspondence remains partial at the measured rates above; elaboration and generated structure still lack complete evidence. See [source correspondence](source-correspondence.md), [Derivation](../src/Agda2SysML/Derivation.hs), and [SourceAlignment](../src/Agda2SysML/SourceAlignment.hs). |
| Unsupported dependencies block strict success and all inspected declarations remain accounted for | Demonstrated for reviewed paths | `Inventory.requirementsFor` computes role-sensitive closure; `Target.discharge` refuses unsupported requirements. The integration suite checks inventory accounting, incomplete `Guarded` output, and matching strict/diagnostic refusals. See [Inventory](../src/Agda2SysML/Inventory.hs) and [Target](../src/Agda2SysML/Target.hs). |
| Valid SysML and source/inventory references without unexplained omissions | Partial | Every measured bundle passes the pinned validator and reference/interval checks. Unavailable source relationships are explicit, but complete correspondence is not attained. Validator acceptance also applies to incomplete diagnostic output. See [Workflow](../src/Agda2SysML/Workflow.hs) and [validator](../validator/README.md). |
| Identical inputs produce stable semantic artifacts | Demonstrated by public regression | [Integration tests](../test/integration.py) compare repeated generation, canonical identities, and semantic bytes after source-line movement. Stable hashes do not supply missing semantic or provenance evidence. |
| Safe formal aggregate and documented implementation correspondence | Demonstrated with stated limits | The aggregate and all eight Haskell suites pass the native validation checks. [Proof coverage](../spec/README.md) and [implementation correspondence](correspondence.md) state abstract laws and trusted adapter boundaries. These are not an end-to-end mechanized proof of the Haskell compiler and SysML semantics. |

Four criteria have supporting evidence for the reviewed scope and three remain
partial. This is an acceptance checklist, not seven equally sized work units.
Full acceptance requires resolving the partial criteria without silently
narrowing the written requirements.

## Prioritized completion checklist

The order below is a proposed sequence. It authorizes no implementation or
change to compatibility, strict-mode behavior, or the release scope.

1. **Define the release acceptance boundary and evidence set.** Preserve the
   written requirements, identify the independently authored projects and mapped
   scopes used for acceptance, and distinguish a preview of the current fragment
   from completion of the full specification. Completion means an agreed matrix
   with explicit pass/fail evidence and a bounded list of required capabilities.
   Any narrower release promise or stricter source-completeness policy needs an
   explicit decision. This decision makes remaining-effort estimates meaningful.
2. **Complete source correspondence for the required accepted fragment.** Address
   specialization transport, implicit arguments, generated/record signatures,
   structural declarations, and outstanding index/relation derivations as separate
   justified rules. In these bundles, 58 whole structural boundaries and 59
   index-contract boundaries remain; a further 28 checked-derived index assertions
   still lack source readiness. `parameterized` derives only 2/151 occurrences and
   `specialized-indexed` only 12/435. Specialization and signature alignment therefore
   deserve attention alongside individual expression rules. Completion means all
   required marked occurrences resolve to adequate source chains, with unchanged
   semantic output and explicit treatment of excluded occurrences.
3. **Implement semantic capabilities required by the acceptance projects.** The
   current native rules exclude open generic/higher-order parameters, recursive
   carriers and helpers, general ordered collection operations, and general
   relation premises. The public `Guarded` and `Relational` failures expose part
   of this gap. Arbitrary runtime universes and arbitrary computed indices also
   remain outside the admitted rules; closed levels and bounded finite helper
   calculations are supported. Each required extension needs its own direct
   target representation, general correspondence laws, and positive/negative
   acceptance checks. An embedded generic interpreter remains outside the chosen
   architecture. See [translation rules](translation-rules.md) and
   [implementation limits](correspondence.md).
4. **Close the target validation and evaluation evidence.** The pinned Pilot
   validates all emitted models, but does not evaluate every quantified relation
   expression and has a returned-construction invocation limitation. Existing
   expression-algebra checks are supplementary evidence. Completion means a
   reviewed correspondence argument and appropriate target-level evidence for
   each required construct, with residual tool limitations stated precisely.
5. **Reconcile documentation and prepare a reviewable release.** Update stale
   status text, consolidate the capability/compatibility matrix, review the
   accumulated implementation diff, and verify the intended committed snapshot
   before publication. For example, the opening of `docs/correspondence.md` still
   calls checked/target catalogs proposals, while its later section and the code
   implement them. The CLI supports Agda 2.8.0 and the native Linux checks passed;
   declared flake outputs alone do not verify every platform. The MIT license and
   build metadata exist. Publication remains a separate authorized action.

The strict completion criterion uses discharged semantic obligations. It does not require
all `sourcePrecision` values to be ready. Changing that criterion is a compatibility
and acceptance-policy decision, already identified in the
[source-correspondence plan](source-correspondence.md#reporting-and-compatibility).

## Verification and reproduction

The implementation tree recorded in the dataset passed
`nix flake check --print-build-logs` on `x86_64-linux`: the safe Agda aggregate,
eight Haskell suites, public artifact/refusal/reproducibility checks, and target
evaluation completed successfully. Other platforms were not checked in that
run. This audit adds documentation and measurement data only.

For each `contracts/*.yaml`, run the following in the pinned development
environment, choosing a fresh output directory for each mapping:

```text
agda2sysml generate --mapping contracts/NAME.yaml --output OUTPUT/NAME --diagnostic
```

Read semantic status and obligations from `correspondence.json`; count
`sourceCorrespondence.targetOccurrences` by `sourcePrecision` and `role`.
Validate the manifest digests and use the existing source-catalog and target-trace
checks in `test/integration.py` to check references and intervals. The evidence
file records the binary digest and every artifact digest for the measured runs.
Runtime bundles and logs are local audit artifacts, not a published release.
