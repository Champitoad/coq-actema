# Setting up the project 

Install opam :
$ sudo apt install opam
And follow instructions. 

Create a local opam switch with ocaml 5.1.1 :
$ opam switch create . 5.1.1
And follow instructions.

Install dependencies :
$ opam install . --deps-only --working-dir

# Building

$ dune build && dune install

