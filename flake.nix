{
  description = "agda2sysml development environment and formal specification checks";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/a7868a727837f3c09cee2ce0ca671c76b1589fed";

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
      environment = system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          agda = pkgs.agda.withPackages (_: [ ]);
          compiler = pkgs.haskellPackages.ghcWithPackages (p: [
            p.Agda p.aeson p.conduit p.libyaml p.optparse-applicative
            p.resourcet p.scientific p.temporary p.cryptohash-sha256
          ]);
          validator = pkgs.callPackage ./nix/validator.nix { };
          generator = pkgs.haskell.lib.overrideCabal
            (pkgs.haskellPackages.callCabal2nix "agda2sysml" (nixpkgs.lib.cleanSource ./.) { })
            (old: { preCheck = (old.preCheck or "") + ''
              export AGDA2SYSML_TEST_VALIDATOR=${validator}
              export AGDA2SYSML_TEST_JAVA=${pkgs.jdk21_headless}/bin/java
            ''; });
          package = pkgs.symlinkJoin {
            name = "agda2sysml-0.1.0";
            paths = [ (pkgs.haskell.lib.justStaticExecutables generator) ];
            nativeBuildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram "$out/bin/agda2sysml" --prefix PATH : ${pkgs.lib.makeBinPath [ validator pkgs.gitMinimal ]}
            '';
          };
        in
        {
          inherit pkgs agda compiler validator generator package;
        };

      # Never copy cached interfaces into the specification check.
      specSource = nixpkgs.lib.cleanSourceWith {
        src = ./spec;
        filter = path: type:
          if type == "directory" then
            builtins.baseNameOf path != "_build"
          else
            nixpkgs.lib.hasSuffix ".agda" path
            || nixpkgs.lib.hasSuffix ".agda-lib" path;
      };
    in
    {
      packages = forAllSystems (system:
        let env = environment system;
        in { default = env.package; agda2sysml = env.package; validator = env.validator; });

      devShells = forAllSystems (system:
        let
          env = environment system;
        in
        {
          default = env.pkgs.mkShell {
            name = "agda2sysml";
            packages = [ env.agda env.compiler env.pkgs.cabal-install env.validator env.pkgs.python3 ];
            AGDA2SYSML_LIBRARIES_FILE = env.pkgs.writeText "agda2sysml-libraries" "";
            AGDA2SYSML_TEST_VALIDATOR = env.validator;
            AGDA2SYSML_TEST_JAVA = "${env.pkgs.jdk21_headless}/bin/java";
          };
        });

      checks = forAllSystems (system:
        let
          env = environment system;
        in
        {
          generator = env.generator;
          integration = env.pkgs.runCommand "agda2sysml-integration" {
            nativeBuildInputs = [ env.package env.agda env.pkgs.python3 env.pkgs.jdk21_headless env.pkgs.nodejs ];
            AGDA2SYSML_LIBRARIES_FILE = env.pkgs.writeText "agda2sysml-libraries" "";
          } ''
            cp -r ${nixpkgs.lib.cleanSource ./.} project
            chmod -R u+w project
            (cd project/contracts && agda Contracts.agda)
            python3 project/test/integration.py ${env.package}/bin/agda2sysml \
              project ${env.validator} ${env.pkgs.jdk21_headless}/bin/java
            mkdir "$out"
          '';
          validator = env.pkgs.runCommand "agda2sysml-validator-check" {
            nativeBuildInputs = [ env.validator ];
          } ''
            echo 'package Contract { attribute def State; }' > valid.sysml
            agda2sysml-validate valid.sysml
            echo 'package Contract { attribute missing : MissingType; }' > invalid.sysml
            if agda2sysml-validate invalid.sysml; then
              echo 'validator accepted an unresolved type' >&2
              exit 1
            fi
            mkdir "$out"
          '';
          spec = env.pkgs.stdenvNoCC.mkDerivation {
            pname = "agda2sysml-spec";
            version = "0.1.0";
            src = specSource;
            nativeBuildInputs = [ env.agda ];
            dontConfigure = true;

            buildPhase = ''
              runHook preBuild
              agda Agda2SysML.agda
              runHook postBuild
            '';

            installPhase = ''
              runHook preInstall
              mkdir -p "$out"
              touch "$out/checked"
              runHook postInstall
            '';
          };
        });
    };
}
