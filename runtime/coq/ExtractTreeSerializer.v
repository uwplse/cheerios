Require Import Cheerios.ExtractTreeSerializerDeps.
Require Import Cheerios.BasicSerializers.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Import ByteListSerializer.

Check serialize_top.
Check serialize.

Definition tree_serialize_top : tree bool -> Serializer.wire :=
  serialize_top _ serialize.

Definition tree_deserialize_top : Serializer.wire -> option (tree bool) :=
  deserialize_top _ deserialize.

Definition tree_serialize_top' (t : tree bool) : Serializer.wire :=
  Serializer.wire_wrap (tree_serialize' _ t).

Extraction "runtime/ocaml/tree_serializer.ml"
           map tree_map'
           tree_serialize_top'
           tree_serialize_top tree_deserialize_top.
