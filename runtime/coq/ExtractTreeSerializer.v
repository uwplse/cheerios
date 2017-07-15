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

Locate serialize.
Check ByteListTree.RWCombinators.RWBasic.bool_Serializer.
Definition tree_serialize_bytelist_top :=
  ByteListBasics.RWClass.serialize_top (tree bool)
                                       (ByteListTree.tree_Serializer ByteListBasics.bool_Serializer). 

Check tree_serialize_bytelist_top.
Definition tree_deserialize_bytelist_top : ByteListWriter.wire -> option (tree bool) :=
  deserialize_top _ deserialize.

Extraction "runtime/ocaml/tree_serializer.ml"
           map tree_map'
           tree_serialize_top'
           tree_serialize_top tree_deserialize_top.
*)