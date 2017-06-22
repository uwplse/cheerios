bit_vector.cmi: bit_vector.mli
	ocamlc bit_vector.mli
serializer_primitives.cmo: bit_vector.cmi serializer_primitives.ml
	ocamlc bit_vector.ml serializer_primitives.ml

bool_pair.cmi: serializer_primitives.cmo
	ocamlc bool_pair.mli
bool_pair.cmo: bool_pair.ml bool_pair.cmi	
	ocamlc bit_vector.ml serializer_primitives.ml bool_pair.ml

bool_pair_test_exec.ml: bool_pair.cmo bool_pair_test.ml
	cat bool_pair.ml bool_pair_test.ml > bool_pair_test_exec.ml
bool_pair_test_exec: bool_pair_test_exec.ml
	ocamlc bit_vector.ml serializer_primitives.ml bool_pair_test_exec.ml \
	-o bool_pair_test

positive.cmi: serializer_primitives.cmo
	ocamlc positive.mli
positive.cmo: positive.ml positive.cmi	
	ocamlc bit_vector.ml serializer_primitives.ml positive.ml

positive_test_exec.ml: positive.cmo positive_test.ml
	cat positive.ml positive_test.ml > positive_test_exec.ml
positive_test_exec: positive_test_exec.ml
	ocamlc bit_vector.ml serializer_primitives.ml positive_test_exec.ml \
	-o positive_test


clean:
	$(RM) bool_pair_test_exec.ml *.cmi *.cmo
