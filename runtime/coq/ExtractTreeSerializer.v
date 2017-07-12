Require Import Cheerios.ExtractTreeSerializerDeps.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Definition tree_serialize_top : tree bool -> Serializer.wire :=
  serialize_top serialize.

Definition tree_deserialize_top : Serializer.wire -> option (tree bool) :=
  deserialize_top deserialize.

Extraction "runtime/ocaml/tree_serializer.ml"
           tree_serialize_top tree_deserialize_top.
