.PHONY: all clean

JSOFOCAML=js_of_ocaml

SOURCES=$(wildcard *.ml)

all: cuty.js

cuty.js: $(SOURCES)
	rm -f cuty.js
	ocamlbuild -use-ocamlfind -plugin-tag "package(js_of_ocaml.ocamlbuild)" cuty.js
	cp _build/cuty.js .

clean:
	ocamlbuild -clean
	rm -f cuty.js
