From Cheerios Require Import Cheerios.
From Coq Require Extraction.

Extract Inlined Constant ascii_serialize => "Serializer_primitives.putByte".
Extract Inlined Constant ascii_deserialize => "Serializer_primitives.getByte".
