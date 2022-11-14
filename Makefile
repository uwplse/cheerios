include Makefile.ml-files

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

$(MLPOSITIVE) $(MLTREE): Makefile.coq
	$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	$(MAKE) -C runtime clean

distclean: clean
	rm -f _CoqProject

.PHONY: default clean install distclean quick
.PHONY: $(MLPOSITIVE) $(MLTREE)

.NOTPARALLEL: $(MLPOSITIVE)
.NOTPARALLEL: $(MLTREE)
