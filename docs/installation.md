# Build and run

The generator is a Haskell executable using Agda 2.8.0 as a library. Generation
also runs a separate Java validator. Python is not a runtime dependency of
generation; it is used by the independent test suite and the optional upstream
Jupyter interface. Nix is one supported way to supply the toolchain, not a
required application runtime.

## Cabal and Java without Nix

Use GHC 9.10.x (the checkpoint uses 9.10.3), Cabal, Git, and a Java 21 JDK.
The host needs the normal native Haskell build prerequisites, including a C
toolchain and the development libraries required by the Cabal dependencies.
For the validator installation below, also install `curl` and `unzip`.

```sh
git clone https://github.com/yovico-ai/agda2sysml.git
cd agda2sysml
cabal update
cabal build exe:agda2sysml
cabal install exe:agda2sysml --installdir="$HOME/.local/bin"
export PATH="$HOME/.local/bin:$PATH"
agda2sysml --version
```

The Cabal file constrains Agda to 2.8.0 and `base` to the GHC 9.10 series.
Other dependencies are resolved by Cabal; this route does not reproduce the
flake's complete dependency lock. A fresh non-Nix installation has not been
verified by the current checkpoint. The offline cached Cabal build used for
that checkpoint is identified separately in its evidence.

Install the pinned upstream Pilot archive and the repository's Java adapter.
Run these commands from the repository root; use an empty installation directory:

```sh
PILOT_HOME="$HOME/.local/share/agda2sysml/pilot-0.58.0"
mkdir -p "$PILOT_HOME"
curl -fL \
  https://github.com/Systems-Modeling/SysML-v2-Pilot-Implementation/releases/download/2026-03/jupyter-sysml-kernel-0.58.0.zip \
  -o "$PILOT_HOME/kernel.zip"
```

Verify the expected **base64 SHA-256**, also pinned in `nix/validator.nix`,
before extracting. This command requires OpenSSL and must succeed:

```sh
test "$(openssl dgst -sha256 -binary "$PILOT_HOME/kernel.zip" | openssl base64 -A)" \
  = 'k/b3yuT//AJB8xCL+aCzo43d3smqJXdYqSDzPcT3Uwg='
```

After confirming it matches:

```sh
unzip "$PILOT_HOME/kernel.zip" -d "$PILOT_HOME"
mkdir -p "$PILOT_HOME/classes"
javac -cp "$PILOT_HOME/sysml/jupyter-sysml-kernel-0.58.0-all.jar" \
  -d "$PILOT_HOME/classes" validator/Validate.java
mkdir -p "$HOME/.local/bin"
cat > "$HOME/.local/bin/agda2sysml-validate" <<'SH'
#!/bin/sh
pilot_dir="$HOME/.local/share/agda2sysml/pilot-0.58.0"
exec java -Djava.awt.headless=true \
  -cp "$pilot_dir/classes:$pilot_dir/sysml/jupyter-sysml-kernel-0.58.0-all.jar" \
  Validate "$pilot_dir/sysml/sysml.library" "$@"
SH
chmod +x "$HOME/.local/bin/agda2sysml-validate"
```

Keep the archive's licenses alongside the installation. Both `java` and
`agda2sysml-validate` must be available on `PATH` during generation. The adapter
validates local files; no server, notebook, or Python installation is required.
On Windows, supply an equivalent launcher invoking the same Java class and
matching library directory; the shell commands above are for Unix systems.

## Optional pinned Nix build

From the checkout, with Nix flakes enabled:

```sh
nix build
export PATH="$PWD/result/bin:$PATH"
agda2sysml --version
```

The packaged executable supplies the validator on its subprocess path.
`nix develop` supplies the compiler, Cabal, validator, and an empty Agda library
registry for this repository's builtin-only inputs. Enter it once for repeated
development commands. Do not use `runghc` to rebuild the application for each
generation; build the executable and reuse it.

The first build can fetch or compile dependencies and run tests. Existing Nix
store paths and Cabal artifacts are reused when their inputs are unchanged.
No system activation or system service is required.

## Generate

Follow the [walkthrough](alpha.md) with `agda2sysml` on `PATH`.
For this repository's builtin-only specification on Unix, set
`AGDA2SYSML_LIBRARIES_FILE=/dev/null`; other projects need their actual Agda
dependency registry. Outputs must have a fresh destination. Large models take
substantially longer to generate and validate than the register example.
