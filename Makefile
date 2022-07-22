all: Makefile.coq api
	@$(MAKE) -f Makefile.coq all 

# Import actema-desktop API

APIDIR = actema-desktop/prover/_build/default/libs/api
APIDIR_LOCAL = src

$(APIDIR_LOCAL)/logic_t.%: $(APIDIR)/logic_t.%
	cp $< $@

$(APIDIR_LOCAL)/logic_b.%: $(APIDIR)/logic_b.%
	cp $< $@

$(APIDIR_LOCAL)/utils.ml: $(APIDIR)/utils.ml
	cp $< $@

api: $(APIDIR_LOCAL)/logic_t.ml $(APIDIR_LOCAL)/logic_t.mli $(APIDIR_LOCAL)/logic_b.ml $(APIDIR_LOCAL)/logic_b.mli $(APIDIR_LOCAL)/utils.ml

# Coq make

ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which coqtop))/
endif

%: Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

clean: Makefile.coq 
	@$(MAKE) -f Makefile.coq clean

cleanall: Makefile.coq 
	@$(MAKE) -f Makefile.coq cleanall

.PHONY: api tests all clean cleanall
