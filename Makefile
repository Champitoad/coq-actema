# --------------------------------------------------------------------
OCAMLBUILD := ocamlbuild -use-ocamlfind
OCAMLBUILD += -plugin-tag "package(js_of_ocaml.ocamlbuild)"

# --------------------------------------------------------------------
.PHONY: all clean __force__

all: html/cuty.js

html/cuty.js: __force__
	rm -f $@ && $(OCAMLBUILD) src/cuty.js
	cp _build/src/cuty.js html/

clean:
	rm -rf _build html/cuty.js
