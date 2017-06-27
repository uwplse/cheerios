bit_vector.cmi: bit_vector.mli
	ocamlc bit_vector.mli
serializer_primitives.cmo: bit_vector.cmi serializer_primitives.ml
primitive_tests: bit_vector.cmi serializer_primitives.ml bit_vector_tests.ml
	ocamlc bit_vector.ml serializer_primitives.ml bit_vector_tests.ml -o bit_vector_tests
%_extracted.cmi: serializer_primitives.cmo
	ocamlc bit_vector.ml serializer_primitives.ml $*_extracted.mli
%_extracted.cmo: %_extracted.ml %_extracted.cmi	
	perl remove_module.pl $* \
	ocamlc bit_vector.ml serializer_primitives.ml $*_extracted.ml

%_test: %_extracted.cmo %_test.ml
	ocamlc bit_vector.ml serializer_primitives.ml $*_extracted.ml $*_test.ml \
	-o $*_test

clean:
	$(RM) *.cmo *.cmi
