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

    atdgen = ocpkgs.atdgen;
    cohttp = ocpkgs.cohttp-lwt-unix;
    sha = ocpkgs.sha;
    ssr = coqPackages.mathcomp-ssreflect;

    coq-actema = pkgs.callPackage ./coq-actema.nix {
      inherit coqPackages;
      prover = prover.packages.x86_64-linux.default;
    };
  in {
    devShell.x86_64-linux = pkgs.mkShell {
      packages = [ coq atdgen cohttp sha ssr coq-actema ];
    };
    packages.x86_64-linux.default = coq-actema;
  };
}
