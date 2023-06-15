{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.11";
  };

  outputs = {self, nixpkgs}:
  let
    pkgs = nixpkgs.legacyPackages.x86_64-linux;
    ocpkgs = pkgs.ocaml-ng.ocamlPackages_4_14;
    coq = pkgs.coq.override {
      version = "8.15.2";
      coq-version = "8.15.2";
      customOCamlPackages = ocpkgs;
    };
    cpkgs = pkgs.mkCoqPackages coq;
    ssr = cpkgs.mathcomp-ssreflect;
  in {
    devShell.x86_64-linux = pkgs.mkShell {
      packages = [ coq ssr ];
    };
  };
}
