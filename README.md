## Project structure 

- frontend/
  Contains the GUI, written in Vue and packaged as a desktop application with Electron. 
  It communicates to the plugin via http, by implementing directly an http server with Node.js.

- prover/
  Contains the logic for the GUI, written in Ocaml.
  It is transpiled to JavaScript with js_of_ocaml, so that it can be run in the browser engine of Electron.

- prover/js/
  Thin wrapper around the prover to ease transpilation to JavaScript.

- plugin/ 
  Contains a Coq plugin, written in Ocaml. 
  It exposes new tactics actema and actema_force that send Coq goals to the frontend (via http), and compile the actions performed by the user in the frontend back to Coq tactics.

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
  Check it is correctly installed by running : $ opam --version

- Update opam : $ opam update

- Create a local opam switch. In the root of the project :
  $ opam switch create . 5.1.1 --repos default,coq-released=https://coq.inria.fr/opam/released

  This will create a switch with ocaml (version 5.1.1) and add a remote repository (needed to fetch mathcomp),
  and install all opam dependencies (but not development-only dependencies such as ocaml-lsp-server).

  Then follow the instructions given by opam. Notably you will have to restart your terminal or run : 
  $ eval $(opam env)

  This creates a "local switch": it will become active automatically each time you enter the project directory.

  Check the switch is setup correctly by running : $ make

- Optionally, install development packages into the switch. 
  On VScode : 
  $ opam install ocamlformat ocaml-lsp-server user-setup
  $ opam user-setup install

  On emacs :
  $ opam install ocamlformat merlin tuareg ocp-indent user-setup 
  $ opam user-setup install

- You'll probably also want to enable formatting on save (formatting uses ocamlformat).
  For VScode : 
  Go to File > Preferences > Settings, type "format" and check the option to format on save.

- Follow the instructions in frontend/README.md to setup the javascript stuff.

- When changing the dependencies (in dune-project), commit the changes (git commit) and then run :
  $ opam install . --deps-only


# Troubleshooting 

- If you get an opam error when creating the switch, don't cleanup the switch and try the following :
  Commit (git commit) your changes, then run :
  $ opam clean
  $ opam install .

- If you get an error when running make/dune build :
    Dynlink error: execution of module initializers in the shared library failed: ...

  Where ... is the name of an ocaml exception (for instance "Not_found"),
  look in file plugin/actema_main.ml, and check that there are no top-level definitions that 
  might be raising errors. 

  The explanation is that when loading the plugin from theories/ with dune, the top-level definitions in 
  the plugin seem to be executed (or at least the definitions in plugin/actema_main.ml). 
  I think this is similar to what would happen in an executable, not in a library. Not sure it is intended or not.

- If you can run "make" without any errors but can't step through Coq files, 
  you might need to set the coqtop path in your editor. 

  If using VScode :
  Go to File > Preferences > Settings, type "coqtop" and set the coqtop bin path to _opam/bin
