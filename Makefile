all: Makefile.coq api
	@$(MAKE) -f Makefile.coq all 

lsp:
	@$(MAKE) clean
	dune build || make

# Import actema-desktop API

APIDIR_LOCAL = src

APIMODS = fo_t fo_b logic_t logic_b utils
APIMODS_SRCS = $(APIMODS:%=$(APIDIR)/%.ml) $(APIMODS:%=$(APIDIR)/%.mli)
APIMODS_SRCS_LOCAL = $(APIMODS:%=$(APIDIR_LOCAL)/%.ml) $(APIMODS:%=$(APIDIR_LOCAL)/%.mli)

$(APIDIR_LOCAL)/%.ml: $(APIDIR)/%.ml
	cp $< $@

$(APIDIR_LOCAL)/%.mli: $(APIDIR)/%.mli
	cp $< $@

api: $(APIMODS_SRCS_LOCAL)

clean-api:
	rm -f $(APIMODS_SRCS_LOCAL)

update-api: clean-api api

# Coq make

ifeq "$(COQBIN)" ""
  COQBIN=$(dir $(shell which coqtop))/
endif

%: Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

install: all
	@$(MAKE) -f Makefile.coq install

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

clean: Makefile.coq 
	@$(MAKE) -f Makefile.coq clean

cleanall: Makefile.coq 
	@$(MAKE) -f Makefile.coq cleanall

.PHONY: lsp api tests all clean cleanall
