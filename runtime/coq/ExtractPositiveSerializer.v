Require Import Cheerios.ExtractPositiveSerializerDeps.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

 Definition positive_serialize_top : positive -> IOStreamWriter.wire :=
   serialize_top serialize.

Definition positive_deserialize_top : IOStreamWriter.wire -> option positive :=
  deserialize_top deserialize.

Extraction "runtime/ocaml/positive_serializer.ml"
           positive_serialize_top positive_deserialize_top.


