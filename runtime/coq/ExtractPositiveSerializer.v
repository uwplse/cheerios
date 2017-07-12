Require Import Cheerios.ExtractPositiveSerializerDeps.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Definition positive_serialize_top : positive -> Serializer.wire :=
  serialize_top (serialize : positive -> Serializer.t).

Definition positive_deserialize_top : Serializer.wire -> option positive :=
  deserialize_top (deserialize : Deserializer.t positive).

Extraction "../ocaml/positive_serializer.ml"
           positive_serialize_top positive_deserialize_top.
