(lang dune 3.13)

(using coq 0.8)

(name coq-actema)

(package
 (name coq-actema)
 (authors
  "Benjamin Werner & Pablo Donato & Pierre-Yves Strub & Mathis Bouverot-Dupuis")
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (synopsis "Integrating the Actema GUI as a tactic")
 (depends
  (coq
   (>= 8.19.1))
  (cohttp-lwt-unix
   (>= 5.0.0))
  (sha
   (>= 1.15.2))
  (atdgen
   (>= 2.0))))

(generate_opam_files)
