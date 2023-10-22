From Cheerios Require Import Cheerios.
From Coq Require Extraction.

Extract Inlined Constant nat_serialize => "(fun i -> Serializer_primitives.putInt (Int32.of_int i))".
Extract Inlined Constant nat_deserialize => "(Serializer_primitives.map Int32.to_int Serializer_primitives.getInt)".
