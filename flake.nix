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
        in
        {
          inherit pkgs agda;
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
      devShells = forAllSystems (system:
        let
          env = environment system;
        in
        {
          default = env.pkgs.mkShell {
            name = "agda2sysml";
            packages = [ env.agda env.pkgs.ghc env.pkgs.cabal-install ];
          };
        });

      checks = forAllSystems (system:
        let
          env = environment system;
        in
        {
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
