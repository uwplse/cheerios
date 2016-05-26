Require Import List.

Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.

Ltac deserializer_unfold :=
  unfold (* list in reverse order so that dependencies get unfolded *)
    sequence,
    fmap,
    fail,
    put,
    get,
    bind,
    ret
  in *.

Ltac serialize_deserialize_id_crush :=
  intros; deserializer_unfold;
  repeat rewrite ?app_assoc_reverse, ?serialize_deserialize_id;
  auto.