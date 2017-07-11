OCAMLBUILD = ocamlbuild -tags 'safe_string' -I . -cflag -g

MLEXTRACTED = positive_extracted.ml positive_extracted.mli
MLFILES = bit_vector.ml bit_vector.mli serializer_primitives.ml

default: cheerios-runtime

$(MLEXTRACTED):
	+$(MAKE) -C .. ocaml-cheerios/$@

positive_test.native: $(MLEXTRACTED) $(MLFILES) positive_test.ml
	perl remove_module.pl positive
	$(OCAMLBUILD) positive_test.native

cheerios-runtime: $(MLFILES) cheerios_runtime.mllib
	$(OCAMLBUILD) cheerios_runtime.cma cheerios_runtime.cmxa cheerios_runtime.cmxs

.PHONY: default clean cheerios-runtime $(MLEXTRACTED)

clean:
	ocamlbuild -clean

.NOTPARALLEL: $(MLEXTRACTED)
