Require Import Cheerios.ExtractTreeSerializerDeps.
Require Import Cheerios.BasicSerializers.
Require Import Cheerios.IOStream.

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Module ByteListBasics := BasicSerializers ByteListWriter ByteListReader.
Module IOStreamBasics := BasicSerializers IOStream ByteListReader.
Module ByteListTree := TreeSerializer ByteListWriter ByteListReader.
Module IOStreamTree := TreeSerializer IOStream ByteListReader.


Definition tree_serialize_bytelist_top : tree bool -> ByteListWriter.wire :=
  ByteListTree.RWCombinators.RWBasic.RWClass.serialize_top
    (tree bool)
    (ByteListTree.tree_Serializer
       ByteListTree.RWCombinators.RWBasic.bool_Serializer)
    (ByteListTree.tree_serialize
       ByteListTree.RWCombinators.RWBasic.bool_Serializer).

Definition tree_deserialize_bytelist_top : ByteListWriter.wire -> option (tree bool) :=
  ByteListTree.RWCombinators.RWBasic.RWClass.deserialize_top
    (tree bool)
    (ByteListTree.tree_Serializer
       ByteListTree.RWCombinators.RWBasic.bool_Serializer)
    (ByteListTree.tree_deserialize
       ByteListTree.RWCombinators.RWBasic.bool_Serializer).

Definition tree_serialize_iostream_top : tree bool -> IOStream.wire :=
  IOStreamTree.RWCombinators.RWBasic.RWClass.serialize_top
    (tree bool)
    (IOStreamTree.tree_Serializer
       IOStreamTree.RWCombinators.RWBasic.bool_Serializer)
    (IOStreamTree.tree_serialize
       IOStreamTree.RWCombinators.RWBasic.bool_Serializer).

Definition tree_deserialize_iostream_top : IOStream.wire -> option (tree bool) :=
  IOStreamTree.RWCombinators.RWBasic.RWClass.deserialize_top
    (tree bool)
    (IOStreamTree.tree_Serializer
       IOStreamTree.RWCombinators.RWBasic.bool_Serializer)
    (IOStreamTree.tree_deserialize
       IOStreamTree.RWCombinators.RWBasic.bool_Serializer).

Extraction "runtime/ocaml/tree_serializer.ml"
           tree_serialize_bytelist_top tree_deserialize_bytelist_top
           tree_serialize_iostream_top tree_deserialize_iostream_top.
