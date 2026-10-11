# Pinned SysML validation

`agda2sysml-validate MODEL.sysml` invokes the official SysML Pilot Implementation
release `2026-03`, distributed in Jupyter SysML Kernel `0.58.0`, with that
archive's matching SysML 2.0 libraries. It reads local files and uses the
headless parser and semantic validator. Syntax errors, semantic errors, and
exceptions produce a nonzero exit; warnings remain visible.

The Nix derivation pins the archive's SHA-256 and Java runtime. The small Java
adapter is MIT licensed as part of this project. The upstream archive is kept
separate and unmodified, including its license files; the upstream tools and
their dependencies retain their respective licenses. The Haskell generator
invokes the validator as a separate process.

The validator establishes target well-formedness. It does not prove semantic
equivalence with an Agda program or discharge a theorem.

The [installation guide](../docs/installation.md) includes a Cabal/Java setup
without Nix. To check the published project models with the installed validator:

```sh
agda2sysml-validate docs/examples/register-workflow.sysml
gzip -dc docs/examples/self.sysml.gz > /tmp/agda2sysml-self.sysml
agda2sysml-validate /tmp/agda2sysml-self.sysml
```

Both models passed validation at this checkpoint; the self translation remains
partial. The self check takes tens of minutes. See the
[checkpoint evidence](../docs/current-state.md) for observed validation results
and the [interactive guide](../docs/interactive-sysml.md#execution-limits) for
the separate execution limitations. Development stages normally use compiler
and independent model tests; full Pilot validation is an explicitly selected
integration or publication checkpoint, not evidence of complete translation.

## Runtime estimates

For planning, allow about **30 seconds to one minute** to validate the small
register model (11.6 KB), and **tens of minutes** for the full self model
(16.6 MB). These are model-specific estimates, not a timeout or an upper bound.
Hardware, JVM configuration, library loading, and model structure affect the
time; validation cost is not proportional to file size.

The reference machine is a shared Linux server with:

- **CPU:** AMD Ryzen 7 5700U with Radeon Graphics, one socket, eight physical
  cores and 16 hardware threads; CPU frequency boost was disabled during the run.
- **Memory:** 59.7 GiB usable RAM reported by Linux (64,132,796,416 bytes).
- **Runtime:** OpenJDK 21; the full self-model validation uses `-Xmx12g`
  (12 GiB maximum Java heap).

These measurements were taken on a shared server, not an isolated benchmark;
other workloads and CPU power settings can affect the elapsed time.

In the latest register run, the entire generation command, including validation
and browser-review serialization, took **16.7 seconds**. The full self model
passed Pilot in **2,108.2 seconds (35 minutes 8 seconds)**.
The duration and result are recorded in
[checkpoint evidence](../docs/current-state.json). Full `agda2sysml generate`
also performs Agda checking and source-correspondence generation: the self run
spent **15 minutes 8 seconds** on those steps before starting Pilot. The entire
self command, including final bundle serialization, took **50 minutes 41 seconds**.

These timings concern **validation**, not execution or simulation of all model
calculations. Pilot can remain silent while validating. A long-running process
has not passed validation until it returns successfully.
