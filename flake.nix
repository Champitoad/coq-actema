{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "nixpkgs";
  };
  outputs = { self, flake-utils, nixpkgs }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        ## If you want to have a "default" package which will be built with just `nix build`, do this instead of `inherit packages;`:
        # packages = packages // { default = packages.<your default package>; };

        devShells.default = pkgs.mkShell {
          env.PKG_CONFIG_PATH = "${pkgs.gmp.dev}/lib/pkgconfig:${pkgs.zlib.dev}/lib/pkgconfig";
          buildInputs = [
            # You can add packages from nixpkgs here
            pkgs.gmp pkgs.zlib
          ];
        };
      });
}
