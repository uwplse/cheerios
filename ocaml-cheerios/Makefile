%_preprocess: %_extracted.ml %_extracted.mli
	perl remove_module.pl $*
%_test: %_preprocess
	ocamlbuild $*_test.native

clean:
	$(RM) -r _build *.native
