{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.05";
    flake-utils.url = "github:numtide/flake-utils";
    prover.url = "./actema-desktop/prover";
  };

  outputs = { self, flake-utils, nixpkgs, prover }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        ocpkgs = pkgs.ocaml-ng.ocamlPackages_4_14;
        coq = pkgs.coq.override {
          version = "8.15.2";
          coq-version = "8.15.2";
          customOCamlPackages = ocpkgs;
        };
        coqPackages = pkgs.mkCoqPackages coq;

        coq-actema = pkgs.callPackage ./coq-actema.nix {
          inherit coqPackages;
        };

        prover-pkg = prover.packages.${system}.default;
      in {
        packages.default = coq-actema;
        devShells.default = pkgs.mkShell {
          inputsFrom = [ coq-actema ];
          packages = [ coq ocpkgs.ocaml-lsp ocpkgs.dune_3 ocpkgs.opam-format ];
          APIDIR = "${prover-pkg}/lib/ocaml/4.14.1/site-lib/prover/api";
        };
        apps.vscoq-actema = {
          type = "app";
          program = "${pkgs.vscodium}/bin/codium";
        };
      }
    );
}
