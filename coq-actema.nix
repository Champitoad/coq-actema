{ lib, version ? null
, coq, coqPackages, ocamlPackages, fetchurl, prover }:
with lib;
  coqPackages.mkCoqDerivation {
  /* namePrefix leads to e.g. `name = coq8.11-mathcomp1.11-multinomials-1.5.2` */
  # namePrefix = [ "coq" ];
  pname = "actema";
  # owner = "coq-community";
  inherit version;
  # defaultVersion =  with versions; switch [ coq.version ] [
  #     { cases = [ "8.15.2" ]; out = "1.0"; }
  #   ] null;w
  release = {
    "1.0".sha256 = "";
  };

  src = ./.;

  mlPlugin = true;

  preBuild =
    let APIDIR = "${prover}/lib/ocaml/4.14.1/site-lib/prover/api"; in ''
      cp ${APIDIR}/{fo_t,fo_b,logic_t,logic_b,utils}.{ml,mli} src/
    '';

  buildInputs = [
    coqPackages.mathcomp-ssreflect
    coq.ocamlPackages.atdgen
    coq.ocamlPackages.sha
    coq.ocamlPackages.cohttp-lwt-unix
  ];

  meta = {
    description = "Integrating the Actema GUI as a tactic";
    license = licenses.cecill-c;
  };
}