Require Import List.
Import ListNotations.

Notation serialize_deserialize_id_spec s d :=
  (forall a (bin : list bool), d (s a ++ bin) = Some (a, bin)).

(* This is the class of serializable types, which is the main entrypoint to
   Cheerios. Instances are required to show that `deserialize` can correctly
   recognize a piece of `serialize`d data at the prefix of an arbitrary
   bitstream. *)
Class Serializer (A : Type) : Type :=
  {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * list bool);
    serialize_deserialize_id : serialize_deserialize_id_spec serialize deserialize
  }.

(* In particular, if there is nothing else in the bitsream, then deserialize and
   serialize are inverses. *)
Lemma serialize_deserialize_id_nil :
  forall A (sA : Serializer A) a, deserialize (serialize a) = Some (a, []).
Proof.
  intros.
  pose proof serialize_deserialize_id a [].
  now rewrite app_nil_r in *.
Qed.