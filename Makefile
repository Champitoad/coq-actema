# --------------------------------------------------------------------
.PHONY: default build install uninstall clean mkproper

DUNEOPTS := --display=short

# --------------------------------------------------------------------
default: build

build:
	dune build $(DUNEOPTS)
	cp _build/default/src/jsprover.js html/

install:
	dune install $(DUNEOPTS)

uninstall:
	dune uninstall $(DUNEOPTS)

clean:
	dune clean $(DUNEOPTS)

mrproper: clean
	git clean -dfXq
