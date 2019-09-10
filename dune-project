(lang dune 1.10)
(using menhir 2.0)
(name prover)

(generate_opam_files true)

(license CeCILL-B)
(authors "Pierre-Yves Strub <pierre-yves@strub.nu>")
(maintainers "pierre-yves@strub.nu")
(homepage "https://gitlab.com/prover-ui/prover")
(bug_reports "https://gitlab.com/prover-ui/prover/issues")
(source (uri "git+https://gitlab.com/prover-ui/prover.git"))

(package
 (name prover)
 (synopsis "A simple prover")
 (depends
  (dune                 (>= 1.10))
  (batteries            (>= 2.5))
  (tyxml                (>= 4.0))
  (tyxml-ppx            (>= 4.0))
  (js_of_ocaml          (>= 2.8))
  (js_of_ocaml-ppx      (>= 2.8))
  (js_of_ocaml-compiler (>= 2.8))
  (menhir               (>= 20181113))))
