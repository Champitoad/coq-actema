# Building mini-prover

## Installing dependencies

We rely on opam (>= 2.0) to install dependencies. See https://opam.ocaml.org/
for more information and for installation instructions.

Once opam is installed & configured, in the mini-prover source root, execute
the following commands:

	> opam pin add -ny .
	> opam install --deps-only prover

When updating the source directory, extra-dependencies can be installed using:

	> opam install --working-dir --deps-only prover
