OCAMLBUILD = ocamlbuild -tags 'safe_string' -I ocaml -cflag -g -lflag -g
OCAMLBUILDTEST = $(OCAMLBUILD) -pkg oUnit -I test

MLPOSITIVEEXTRACTED = ocaml/positive_serializer.ml ocaml/positive_serializer.mli
MLTREEEXTRACTED = ocaml/tree_serializer.ml ocaml/tree_serializer.mli

MLFILES = ocaml/bit_vector.ml ocaml/bit_vector.mli \
 ocaml/serializer_primitives.ml ocaml/serializer_primitives.mli

default: cheerios-runtime

$(MLPOSITIVEEXTRACTED) $(MLTREEEXTRACTED):
	+$(MAKE) -C .. runtime/$@

positive_test.native: $(MLPOSITIVEEXTRACTED) $(MLFILES) test/positive_test.ml
	$(OCAMLBUILDTEST) positive_test.native

tree_test.native: $(MLTREEXTRACTED) $(MLFILES) test/tree_test.ml
	$(OCAMLBUILDTEST) tree_test.native

tree_test.byte: $(MLTREEXTRACTED) $(MLFILES) test/tree_test.ml
	$(OCAMLBUILDTEST) tree_test.byte

cheerios-runtime: $(MLFILES) ocaml/cheerios_runtime.mllib
	$(OCAMLBUILD) cheerios_runtime.cma cheerios_runtime.cmxa cheerios_runtime.cmxs

.PHONY: default clean cheerios-runtime $(MLPOSITIVEEXTRACTED) $(MLTREEEXTRACTED)

clean:
	ocamlbuild -clean

.NOTPARALLEL: $(MLPOSITIVEEXTRACTED)
.NOTPARALLEL: $(MLTREEEXTRACTED)
