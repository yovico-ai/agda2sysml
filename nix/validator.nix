{ stdenvNoCC, fetchurl, unzip, jdk21_headless, makeWrapper, lib }:
stdenvNoCC.mkDerivation {
  pname = "agda2sysml-validator";
  version = "2026-03";
  src = fetchurl {
    url = "https://github.com/Systems-Modeling/SysML-v2-Pilot-Implementation/releases/download/2026-03/jupyter-sysml-kernel-0.58.0.zip";
    hash = "sha256-k/b3yuT//AJB8xCL+aCzo43d3smqJXdYqSDzPcT3Uwg=";
  };
  nativeBuildInputs = [ unzip jdk21_headless makeWrapper ];
  sourceRoot = ".";
  dontConfigure = true;
  buildPhase = ''
    runHook preBuild
    mkdir classes
    cp ${../validator/Validate.java} Validate.java
    javac -cp sysml/jupyter-sysml-kernel-0.58.0-all.jar -d classes Validate.java
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p "$out/share/agda2sysml-validator" "$out/bin"
    cp -r classes sysml LICENSE LICENSE-GPL "$out/share/agda2sysml-validator/"
    makeWrapper ${jdk21_headless}/bin/java "$out/bin/agda2sysml-validate" \
      --add-flags "-cp $out/share/agda2sysml-validator/classes:$out/share/agda2sysml-validator/sysml/jupyter-sysml-kernel-0.58.0-all.jar Validate" \
      --add-flags "$out/share/agda2sysml-validator/sysml/sysml.library"
    runHook postInstall
  '';
  # Upstream distribution and its dependencies retain their own licenses.
  meta = {
    description = "Headless SysML validator using the official 2026-03 pilot distribution";
    homepage = "https://github.com/Systems-Modeling/SysML-v2-Pilot-Implementation";
    license = with lib.licenses; [ epl20 lgpl3Only ];
    platforms = lib.platforms.unix;
    mainProgram = "agda2sysml-validate";
  };
}
