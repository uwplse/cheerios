Require Import Cheerios.ExtractPositiveSerializerDeps.
Require Import Cheerios.IOStream.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.


Module ByteListBasics := BasicSerializers ByteListWriter ByteListReader.
Module IOStreamBasics := BasicSerializers IOStream ByteListReader.

Definition positive_serialize_bytelist_top : positive -> ByteListWriter.wire :=
  @ByteListBasics.RWClass.serialize_top positive _ ByteListBasics.RWClass.serialize.

Definition positive_deserialize_bytelist_top : ByteListWriter.wire -> option positive :=
  @ByteListBasics.RWClass.deserialize_top _ _ ByteListBasics.RWClass.deserialize.

Definition positive_serialize_iostream_top : positive -> IOStream.wire :=
  @IOStreamBasics.RWClass.serialize_top positive _ IOStreamBasics.RWClass.serialize.

Definition positive_deserialize_iostream_top : ByteListWriter.wire -> option positive :=
  @ByteListBasics.RWClass.deserialize_top _ _ IOStreamBasics.RWClass.deserialize.

Extraction "runtime/ocaml/positive_serializer.ml"
           positive_serialize_bytelist_top positive_deserialize_bytelist_top
           positive_serialize_iostream_top positive_deserialize_iostream_top.

