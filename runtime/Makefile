OCAMLBUILD = ocamlbuild -tags 'safe_string' -I ocaml -cflag -g
OCAMLBUILDTEST = $(OCAMLBUILD) -pkg oUnit -I test

MLEXTRACTED = ocaml/positive_serializer.ml ocaml/positive_serializer.mli

MLFILES = ocaml/bit_vector.ml ocaml/bit_vector.mli \
 ocaml/serializer_primitives.ml ocaml/serializer_primitives.mli

default: cheerios-runtime

$(MLEXTRACTED):
	+$(MAKE) -C .. runtime/$@

positive_test.native: $(MLEXTRACTED) $(MLFILES) script/remove_module.pl test/positive_test.ml
	perl script/remove_module.pl ocaml/positive_serializer
	$(OCAMLBUILDTEST) positive_test.native

cheerios-runtime: $(MLFILES) ocaml/cheerios_runtime.mllib
	$(OCAMLBUILD) cheerios_runtime.cma cheerios_runtime.cmxa cheerios_runtime.cmxs

.PHONY: default clean cheerios-runtime $(MLEXTRACTED)

clean:
	ocamlbuild -clean

.NOTPARALLEL: $(MLEXTRACTED)
