# --------------------------------------------------------------------
OCAMLBUILD := ocamlbuild -use-ocamlfind
OCAMLBUILD += -plugin-tag "package(js_of_ocaml.ocamlbuild)"

JSPKG := notifyjs\#^0.4 hammerjs\#^2.0.0 jquery\#^2.0.0

# --------------------------------------------------------------------
.PHONY: all clean 3rdparty __force__

all: html/cuty.js

html/cuty.js: __force__
	rm -f $@ && $(OCAMLBUILD) src/cuty.js
	cp _build/src/cuty.js html/

3rdparty:
	cd html && bower install $(JSPKG)

clean:
	rm -rf _build html/cuty.js
