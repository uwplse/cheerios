COQVERSION := $(shell coqc --version|egrep "version (8\\.5|8\\.6)")

ifeq "$(COQVERSION)" ""
$(error "Cheerios is only compatible with Coq version 8.5 or 8.6")
endif

COQPROJECT_EXISTS=$(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

MLFILES = cheerios-runtime/ocaml/positive_extracted.ml cheerios-runtime/ocaml/positive_extracted.mli

default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra '$(MLFILES)' \
	    'cheerios-runtime/coq/ExtractPositiveSerializer.v cheerios-runtime/coq/ExtractPositiveSerializerDeps.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) cheerios-runtime/coq/ExtractPositiveSerializer.v'

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	$(MAKE) -C cheerios-runtime clean

.PHONY: default clean install

.NOTPARALLEL: $(MLFILES)
