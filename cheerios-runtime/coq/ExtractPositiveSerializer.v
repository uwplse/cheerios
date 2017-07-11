Require Import ExtractCheerios.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Definition positive_serialize_top : positive -> Serializer.wire :=
  serialize_top (serialize : positive -> Serializer.t).

Definition positive_deserialize_top : Serializer.wire -> option positive :=
  deserialize_top (deserialize : Deserializer.t positive).

Extraction "ocaml-cheerios/positive_extracted.ml"
           positive_serialize_top positive_deserialize_top.
