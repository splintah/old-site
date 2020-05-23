{ nixpkgs ? import <nixpkgs> { }
, compiler ? "ghc865"
}:
let haskell = nixpkgs.pkgs.haskell.packages.${compiler}.override {
      overrides = self: super: {
        hakyll-series = nixpkgs.pkgs.haskell.lib.unmarkBroken super.hakyll-series;
      };
    };
in haskell.callPackage ./blog.nix { }
