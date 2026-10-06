# agda2sysml

Generate SysML models from Agda specifications.

agda2sysml is a standalone project for making formally specified systems easier
to explore through SysML. Agda specifications are the source of truth; generated
models should expose their structure and behavior while preserving links to the
original definitions.

## Project goals

- Generate SysML from Agda types, definitions, and formal contracts.
- Keep generated elements traceable to their Agda source.
- Make representation limits explicit when an Agda definition cannot be
  faithfully expressed in SysML.
- Support reproducible generation as specifications evolve.

## Status

The initial written and formal specifications are available for review:

- [Project specification](SPECIFICATION.md)
- [Project mapping format](docs/project-mapping.md)
- [Formal laws and verification instructions](spec/README.md)

The proposed generator uses Haskell and targets SysML 2.0. Its implementation,
compiler adapter, and SysML emitter are not yet available. The Agda core proves
the transformation and coverage laws described in the formal specification;
it does not establish end-to-end compiler correctness.

## Development

With Nix flakes enabled, run `nix develop` from the repository root for the
pinned Agda, GHC, and Cabal environment. Run `nix flake check` to type-check the
complete formal specification in an isolated build without cached interfaces.
See the [formal specification instructions](spec/README.md) for interactive work.

## License

MIT. See [LICENSE](LICENSE).
