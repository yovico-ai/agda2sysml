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

The project is at its initial setup stage. A generator, supported Agda subset,
SysML version, and usage instructions have not yet been implemented or defined.

## License

MIT. See [LICENSE](LICENSE).
