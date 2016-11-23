# --------------------------------------------------------------------
OCAMLBUILD := ocamlbuild -use-ocamlfind
OCAMLBUILD += -plugin-tag "package(js_of_ocaml.ocamlbuild)"

JSPKG := \
	notifyjs\#^0.4 \
	hammerjs\#^2.0.0 \
	jquery\#^2.0.0 \
	bootstrap\#^3.0.0 \
	MathJax\#^2.7

# --------------------------------------------------------------------
UNAMES := $(shell uname -s)
OPEN   := /bin/false

ifeq ($(UNAMES),Linux)
OPEN := xdg-open
else ifeq ($(UNAMES),Darwin)
OPEN := open
endif

# --------------------------------------------------------------------
.PHONY: all clean 3rdparty open __force__

all: html/cuty.js

html/cuty.js: __force__
	rm -f $@ $(@:.js=.map) && $(OCAMLBUILD) src/cuty.js
	@for i in js map; do [ ! -f _build/src/cuty.$$i ] || \
	  cp -v _build/src/cuty.$$i html/; \
	done

3rdparty:
	cd html && bower install $(JSPKG)

open:
	cd html && $(OPEN) index.html

clean:
	rm -rf _build html/cuty.js
