# --------------------------------------------------------------------
OCAMLBUILD := ocamlbuild -use-ocamlfind
OCAMLBUILD += -plugin-tag "package(js_of_ocaml.ocamlbuild)"

# --------------------------------------------------------------------
.PHONY: all build clean __force__

all: build

build: main.native
	@true

clean:
	rm -rf _build

# --------------------------------------------------------------------
%.native: __force__
	rm -f $@ && $(OCAMLBUILD) src/$@

%.byte: __force__
	rm -f $@ && $(OCAMLBUILD) src/$@

libs/%.cmx: __force__
	$(OCAMLBUILD) $@
