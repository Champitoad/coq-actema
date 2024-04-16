## Project structure 

- frontend/
  Contains the GUI, written in javascript and using Vue and electron. 

- prover/
  Contains the logic for the GUI, written in Ocaml. It communicates to the plugin via http.

- prover/js/
  Thin wrapper around the prover to ease compilation to javascript.

- plugin/ 
  Contains the Coq plugin, written in Ocaml. It communicates to the prover via http. 

- api/
  Contains the data format used to communicate between the prover and the plugin.
  It uses atdgen to generate Ocaml code.

- theories/
  Coq tactics that are invoked from the plugin.

## Development workflow

- Build the ocaml code. From the root :
  $ make

- Launch the frontend. From frontend/, and in another terminal :
  $ npm run electron:serve

- Step through a coq file until you reach an actema tactic.

There is no need to re-launch the frontend every time ! 
The frontend will automatically reload (hot-reload) when changing files in frontend/src
or when running make.

## Setting up a development environment

- Install opam (e.g. on ubuntu : $ sudo apt install opam). 

- Create a local opam switch. In the root of the project :
  $ opam switch create . 5.1.1 --repos default,coq-released=https://coq.inria.fr/opam/released --with-test --with-doc

  This will create a switch with ocaml (version 5.1.1) and add a remote repository (needed to fetch mathcomp),
  and install all opam dependencies (including development-only dependencies such as ocaml-lsp-server).

  This is a "local switch": it will become active each time you enter the project directory.

- If using VScode : set the coqtop path. 
  Go to File > Preferences > Settings, type "coqtop" and set the coqtop bin path to _opam/bin

  You'll probably also want to enable formatting on save (formatting uses ocamlformat).
  Go to File > Preferences > Settings, type "format" and check the option to format on save.

- Follow the instructions in frontend/README.md to setup the javascript stuff.

## Build instructions 

- To build :
  $ dune build && dune install

  To step through coq files in VScode, it is important to run "dune install" first !
  
- When changing the dependencies (in dune-project) run :
  $ opam install . --deps-only --with-test --with-doc


# Troubleshooting 

- If you get an opam error when creating the switch, don't cleanup the switch and try the following :
  Commit (git commit) your changes, then run :
  $ opam clean
  $ opam install .

- If you get an error when running dune build :
    Dynlink error: execution of module initializers in the shared library failed: ...

  Where ... is the name of an ocaml exception (for instance "Not_found"),
  look in file plugin/actema_main.ml, and check that there are no top-level definitions that 
  might be raising errors. 

  The explanation is that when loading the plugin from theories/ with dune, the top-level definitions in 
  the plugin seem to be executed (or at least the definitions in plugin/actema_main.ml). 
  I think this is similar to what would happen in an executable, not in a library. Not sure it is intended or not.
