bit_vector.cmi: bit_vector.mli
	ocamlopt bit_vector.mli
serializer_primitives.cmo: bit_vector.cmi serializer_primitives.ml
primitive_tests: bit_vector.cmi serializer_primitives.ml bit_vector_tests.ml
	ocamlopt bit_vector.ml serializer_primitives.ml bit_vector_tests.ml -o bit_vector_tests
%_extracted.cmi: serializer_primitives.cmo
	ocamlopt bit_vector.ml serializer_primitives.ml $*_extracted.mli
%_extracted.cmo: %_extracted.ml %_extracted.cmi	
	perl remove_module.pl $* \
	ocamlopt bit_vector.ml serializer_primitives.ml $*_extracted.ml

%_test: %_extracted.cmo %_test.ml
	ocamlopt bit_vector.ml serializer_primitives.ml $*_extracted.ml $*_test.ml \
	-o $*_test

clean:
	$(RM) *.cmo *.cmi
