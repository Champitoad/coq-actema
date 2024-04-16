# Build everything (except the frontend, which you should launch via npm run electron:serve).
all:
	dune build
# Install the dune stuff. This is required to be able to step
# through coq files using VScode/coqtop.
	dune install
# Copy the file generates by js_of_ocaml to the frontend.
	cp -f _build/default/jsprover/jsprover.js frontend/public/prover.js

clean:
	dune clean