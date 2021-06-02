{
  description = "Flake for splintah.github.io.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-20.03";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        compiler = "ghc865";
        pkgs = nixpkgs.legacyPackages.${system};
        haskellPackages = pkgs.haskell.packages.${compiler}.override {
          overrides = final: prev: {
            hakyll = pkgs.haskell.lib.unmarkBroken prev.hakyll;
            hakyll-series = pkgs.haskell.lib.unmarkBroken prev.hakyll-series;
          };
        };
      in {
        packages.blog = haskellPackages.callPackage ./blog.nix { };
        defaultPackage = self.packages.${system}.blog;

        defaultApp = self.apps.${system}.site;
        apps.site = {
          type = "app";
          program = "${self.defaultPackage.${system}}/bin/site";
        };

        apps.build = {
          type = "app";
          program = toString (pkgs.writeScript "build"
            "${self.defaultPackage.${system}}/bin/site build");
        };
      });
}
