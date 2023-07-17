{ lib
, version ? null
, coq
, coqPackages
, ocamlPackages
}:
with lib;
coqPackages.mkCoqDerivation {
  pname = "actema";
  # owner = "coq-community";
  inherit version;
  defaultVersion =
    let oneOf = a: v: builtins.elem v a; in
    coqPackages.lib.switch coq.coq-version [
      {
        case = oneOf [ "8.10" "8.11" "8.12" "8.13" "8.13.1" "8.14" "8.15" "8.16" "8.17" ];
        out = "0.1.0";
      }
    ]
      null;
  release = {
    "0.1.0".sha256 = "";
  };

  src = ./.;

  mlPlugin = true;

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
