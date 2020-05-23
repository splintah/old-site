{ mkDerivation
, stdenv
, base
, hakyll
, pandoc
, pandoc-types
, containers
, hakyll-series
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
    hakyll-series
  ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
