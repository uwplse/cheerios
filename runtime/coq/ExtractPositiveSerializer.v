Require Import Cheerios.ExtractPositiveSerializerDeps.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Import ByteListSerializer.

Definition positive_serialize_top : positive -> Serializer.wire :=
  serialize_top _ serialize.

Definition positive_serialize_top_tr :=
  serialize_top _ (fun p => positive_serialize_rec p Serializer.empty).

Definition positive_deserialize_top : Serializer.wire -> option positive :=
  deserialize_top _ (deserialize : Deserializer.t positive).

Extraction "runtime/ocaml/positive_serializer.ml"
           positive_serialize_top positive_deserialize_top
           positive_serialize_top_tr.
