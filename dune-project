(lang dune 3.13)

(using coq 0.8)

(using menhir 2.0)

(name coq-actema)

; The .opam file is regenerated each time you call dune build.
; To manually regenerate the .opam file, run :
; $ dune build coq-actema.opam

(generate_opam_files true)

(package
 (name coq-actema)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors
  "Benjamin Werner, Pierre-Yves Strub, Pablo Donato, Mathis Bouverot-Dupuis")
 (homepage "https://github.com/Champitoad/coq-actema")
 (bug_reports "https://github.com/Champitoad/coq-actema/issues")
 (synopsis "Integrating the Actema GUI as a Coq tactic")
 (depends
  (atdgen
   (>= 2.15.0))
  (coq
   (= 8.19.1))
  (coq-mathcomp-ssreflect
   (= 2.2.0))
  (cohttp-lwt-unix
   (>= 5.3.0))
  (lwt_ppx
   (>= 2.1.0))
  (sha
   (>= 1.15.2))
  (tyxml
   (>= 4.6.0))
  (tyxml-ppx
   (>= 4.6.0))
  (ocamlgraph
   (>= 2.1.0))
  (base64
   (>= 3.5.1))
  (js_of_ocaml
   (>= 5.7.2))
  (js_of_ocaml-ppx
   (>= 5.7.2))
  (batteries
   (>= 3.8.0))))
