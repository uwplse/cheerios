Require Import Cheerios.ExtractPositiveSerializerDeps.
Require Import Cheerios.IOStream.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Module ByteListBasics := BasicSerializers ByteListWriter ByteListReader ByteListSerializer.
Module IOStreamBasics := BasicSerializers IOStream ByteListReader IOStreamSerializer.

Definition positive_serialize_bytelist_top : positive -> ByteListWriter.wire :=
  ByteListSerializer.serialize_top ByteListSerializer.serialize.

Definition positive_deserialize_bytelist_top : ByteListWriter.wire -> option positive :=
  ByteListSerializer.deserialize_top ByteListSerializer.deserialize.

Definition positive_serialize_iostream_top : positive -> IOStream.wire :=
  IOStreamSerializer.serialize_top IOStreamSerializer.serialize.

Definition positive_deserialize_iostream_top : IOStream.wire -> option positive :=
  IOStreamSerializer.deserialize_top IOStreamSerializer.deserialize.

Extraction "runtime/ocaml/positive_serializer.ml"
           positive_serialize_bytelist_top positive_deserialize_bytelist_top
           positive_serialize_iostream_top positive_deserialize_iostream_top.

