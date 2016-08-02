Require Import List.
Import ListNotations.

Require Import Cheerios.Monoid.


Notation serialize_deserialize_id_spec s d :=
  (forall a bin, d (s a +++ bin) = Some (a, bin)).

(* This is the class of serializable types, which is the main entrypoint to
   Cheerios. Instances are required to show that `deserialize` can correctly
   recognize a piece of `serialize`d data at the prefix of an arbitrary
   bitstream. *)
Class Serializer (bin : Type) {mbin : Monoid bin} (A : Type) : Type :=
  {
    serialize : A -> bin;
    deserialize : bin -> option (A * bin);
    serialize_deserialize_id : serialize_deserialize_id_spec serialize deserialize
  }.

(* In particular, if there is nothing else in the bitsream, then deserialize and
   serialize are inverses. *)
Lemma serialize_deserialize_id_nil :
  forall bin (mbin : Monoid bin) A (sA : Serializer bin A) a,
    deserialize (serialize a) = Some (a, mempty).
Proof.
  intros.
  pose proof serialize_deserialize_id a mempty.
  now rewrite @mappend_mempty_r in *.
Qed.
