OCAMLBUILD = ocamlbuild -tags 'safe_string' -I . -cflag -g

MLEXTRACTED = positive_extracted.ml positive_extracted.mli
MLFILES = bit_vector.ml bit_vector.mli serializer_primitives.ml positive_test.ml

default: positive_test.native

$(MLEXTRACTED):
	+$(MAKE) -C .. ocaml-cheerios/$@

positive_test.native: $(MLEXTRACTED) $(MLFILES)
	perl remove_module.pl positive
	$(OCAMLBUILD) positive_test.native

.PHONY: default clean $(MLEXTRACTED)

clean:
	ocamlbuild -clean

.NOTPARALLEL: $(MLEXTRACTED)
