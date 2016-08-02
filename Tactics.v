Require Import List.

From Cheerios Require Import Monoid Core DeserializerMonad.

Ltac deserializer_unfold :=
  unfold (* list in reverse order so that dependencies get unfolded *)
    unwrap,
    liftD4,
    liftD3,
    liftD2,
    liftD1,
    sequence,
    fmap,
    push,
    fail,
    put,
    get,
    bind,
    ret
  in *.

Hint Rewrite
     @mappend_assoc
     @mappend_mempty_l
     @mappend_mempty_r
     @serialize_deserialize_id
     @serialize_deserialize_id_nil
  : cheerios.


Ltac cheerios_crush :=
  intros; deserializer_unfold;
  autorewrite with cheerios;
  auto.
