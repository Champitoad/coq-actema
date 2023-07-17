{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.05";
    prover.url = "./actema-desktop/prover";
  };

  outputs = { self, nixpkgs, prover }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
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

      prover-pkg = prover.packages.x86_64-linux.default;
    in
    {
      packages.x86_64-linux.default = coq-actema;
      devShell.x86_64-linux = pkgs.mkShell {
        inputsFrom = [ coq-actema ];
        packages = [ coq ocpkgs.ocaml-lsp ];
        APIDIR = "${prover-pkg}/lib/ocaml/4.14.1/site-lib/prover/api";
      };
      apps.x86_64-linux.vscoq-actema = {
        type = "app";
        program = "${pkgs.vscodium}/bin/codium";
      };
    };
}
