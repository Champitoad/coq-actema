# --------------------------------------------------------------------
OCAMLBUILD := ocamlbuild -use-ocamlfind -classic-display
OCAMLBUILD += -plugin-tag "package(js_of_ocaml.ocamlbuild)"

# --------------------------------------------------------------------
.PHONY: all build top clean __force__

all: build

build: main.native
	@true

top:
	$(OCAMLBUILD) src/ljmooc.top

clean:
	rm -rf _build ljmooc.top main.native

# --------------------------------------------------------------------
%.native: __force__
	rm -f $@ && $(OCAMLBUILD) src/$@

%.byte: __force__
	rm -f $@ && $(OCAMLBUILD) src/$@

libs/%.cmx: __force__
	$(OCAMLBUILD) $@
