Require Import Cheerios.ExtractTreeSerializerDeps.
Require Import Cheerios.BasicSerializers.
Require Import Cheerios.IOStream.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Module ByteListTree := TreeSerializer ByteListWriter ByteListReader ByteListSerializer.
Module IOStreamTree := TreeSerializer IOStream ByteListReader IOStreamSerializer.

Definition tree_serialize_bytelist_top : tree bool -> ByteListWriter.wire :=
  ByteListSerializer.serialize_top ByteListSerializer.serialize.

Definition tree_deserialize_bytelist_top : ByteListWriter.wire -> option (tree bool) :=
  ByteListSerializer.deserialize_top ByteListSerializer.deserialize.

Definition tree_serialize_iostream_top : tree bool -> IOStream.wire :=
  IOStreamSerializer.serialize_top IOStreamSerializer.serialize.

Definition tree_deserialize_iostream_top : IOStream.wire -> option (tree bool) :=
  IOStreamSerializer.deserialize_top IOStreamSerializer.deserialize.

Extract Inlined Constant IOStreamSerializer.deserialize_top => "Serializer_primitives.deserialize_top".
Extract Inlined Constant ByteListSerializer.deserialize_top => "Serializer_primitives.deserialize_top".

Extraction "runtime/ocaml/tree_serializer.ml"
           tree_serialize_bytelist_top tree_deserialize_bytelist_top
           tree_serialize_iostream_top tree_deserialize_iostream_top.
