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
