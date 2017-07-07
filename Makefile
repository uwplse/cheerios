COQVERSION := $(shell coqc --version|egrep "version (8\\.5|8\\.6)")

ifeq "$(COQVERSION)" ""
$(error "Cheerios is only compatible with Coq version 8.5 or 8.6")
endif

COQPROJECT_EXISTS=$(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

MLFILES = ocaml-cheerios/positive_extracted.ml ocaml-cheerios/positive_extracted.mli

default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra '$(MLFILES)' \
	    'Extraction.v ExtractionDeps.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) Extraction.v'

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq

.PHONY: default clean install

.NOTPARALLEL: $(MLFILES)
