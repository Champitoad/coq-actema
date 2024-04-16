# Build everything (except the frontend)
all:
	dune build
# Install the dune stuff. This is required to be able to step
# through coq files using VScode/coqtop.
	dune install
# Copy the file generates by js_of_ocaml to the frontend.
	cp -f _build/default/jsprover/jsprover.js frontend/public/prover.js

# Launch the actema GUI.
# You might want to execute this from a separate terminal.
actema:
	${NVM_DIR}/nvm.sh && nvm use && nvm -v
    
clean:
	dune clean