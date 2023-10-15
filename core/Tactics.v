From Coq Require Import List.
From Cheerios Require Import Core.
From Cheerios Require Import DeserializerMonad.
From Cheerios Require Import Types.

Ltac cheerios_crush := intros; autorewrite with cheerios; auto.

#[global]
Hint Rewrite <- app_assoc : cheerios.
#[global]
Hint Rewrite
 IOStreamWriter.empty_unwrap IOStreamWriter.putByte_unwrap
 IOStreamWriter.append_unwrap
 ByteListReader.getByte_unwrap ByteListReader.bind_unwrap ByteListReader.ret_unwrap
 ByteListReader.map_unwrap @ByteListReader.fold_unwrap : cheerios.
