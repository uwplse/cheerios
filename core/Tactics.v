Require Import List.

Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.

Ltac cheerios_crush := intros; autorewrite with cheerios; auto.

Hint Rewrite app_ass 
     Serializer.empty_unwrap Serializer.putByte_unwrap
     Serializer.append_unwrap Deserializer.getByte_unwrap
     Deserializer.bind_unwrap Deserializer.ret_unwrap
     Deserializer.map_unwrap @Deserializer.fold_unwrap : cheerios.
