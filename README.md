# Setting up a development environment

- Install opam (e.g. on ubuntu : $ sudo apt install opam). 

- Create a local opam switch. In the root of the project :
  $ opam switch create . 5.1.1 --repos default,coq-released=https://coq.inria.fr/opam/released --with-test --with-doc

  This will create a switch with ocaml (version 5.1.1) and add a remote repository (needed to fetch mathcomp),
  and install all opam dependencies (including development-only dependencies such as ocaml-lsp-server).

  This is a "local switch": it will become active each time you enter the project directory.

- If using VScode : set the coqtop path. 
  Go to File > Preferences > Settings, type "coqtop" and set the coqtop bin path to _opam/bin

# Build instructions 

- To build :
  $ dune build && dune install

  To step through coq files in VScode, it is important to run "dune install" first !
  
- When changing the dependencies (in dune-project) run :
  $ opam install . --deps-only --with-test --with-doc

  If this doesn't do anything, try commiting (git commit) your local changes first.

# Troubleshooting 

- If you get an error :
    Dynlink error: execution of module initializers in the shared library failed: ...

  Where ... is the name of an ocaml exception (for instance "Not_found"),
  look in file plugin/actema_main.ml, and check that there are no top-level definitions that 
  might be raising errors. 

  The explanation is that when loading the plugin from theories/ with dune, the top-level definitions in 
  the plugin seem to be executed (or at least the definitions in plugin/actema_main.ml). 
  I think this is similar to what would happen in an executable, not in a library. Not sure it is intended or not.
