{ mkDerivation
, stdenv
, base
, hakyll
, pandoc
, pandoc-types
, containers
}:
mkDerivation {
  pname = "blog";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    base
    hakyll
    pandoc-types
    pandoc
    containers
  ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
