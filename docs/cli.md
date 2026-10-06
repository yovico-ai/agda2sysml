# Command line and artifact contract

The command forms are:

```text
agda2sysml inspect --mapping FILE --output DIRECTORY
agda2sysml generate --mapping FILE --output DIRECTORY
agda2sysml generate --mapping FILE --output DIRECTORY --diagnostic
```

All relative project paths are interpreted relative to the mapping file.
The output directory must not already exist. Input source is never edited.
Commands perform no publication or upload. They operate on the configured local
libraries and pinned validator installation.

`inspect` checks input, resolves mappings, and emits the inventory, diagnostics,
and manifest. It succeeds when checking and mapping validation finish, even when
the inventory identifies translation features requiring additional support.

`generate` is strict unless `--diagnostic` is supplied. Strict generation succeeds
only after every required obligation has evidence and the target validator
accepts the model. Incomplete diagnostic output is never marked complete.

Exit status is 0 for a completed requested operation, 2 for an incomplete
translation, and 1 for invalid configuration, failed checking, invalid output,
validator failure, or I/O failure. `--help` and `--version` exit successfully.

Artifacts use schema version 1: `inventory.json`, `diagnostics.json`,
`manifest.json`, and, for generation, `correspondence.json` and `model.sysml`.
Each JSON document has `schemaVersion: 1`. Definitions have canonical identities,
kind, module, declared type, source spans, checking assumptions, dependencies,
and representation obligations. Diagnostics have code, severity, message,
affected symbol/model where known, and source or mapping location.

The manifest records content digests, mapping and toolchain identities, inspected
and required scopes, mode, completion, and validator identity. Source locations
are relative to labeled library roots; absolute local paths are not serialized.
Stable IDs derive from library identity and qualified declaration identity,
never source line numbers or timestamps.

Failed generation may produce a diagnostic report, but must never leave a
success manifest or a model labeled complete. Artifact publication is staged in
a sibling temporary directory and finalized only after serialization succeeds.
An output directory that appeared after validation must not be overwritten.
