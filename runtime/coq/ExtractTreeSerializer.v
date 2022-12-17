From Cheerios Require Import ExtractTreeSerializerDeps.
From Cheerios Require Import BasicSerializers.
From Coq Require Import ZArith.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

Definition tree_serialize : tree bool -> IOStreamWriter.t := serialize.

Definition tree_deserialize : ByteListReader.t (tree bool) := deserialize.

Definition tree_serialize_top : tree bool -> IOStreamWriter.wire :=
  fun t => serialize_top (serialize t).

Definition tree_deserialize_top : IOStreamWriter.wire -> option (tree bool) :=
  deserialize_top deserialize.

Extraction "runtime/test/tree_serializer.ml" tree_serialize tree_deserialize tree_serialize_top tree_deserialize_top.

