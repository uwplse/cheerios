Require Import List.

Class Serializer A :=
  {
    serialize: A -> (list bool);
    deserialize: list bool -> option (A * list bool);
    Serialize_reversible: forall (x: A) (bin: list bool),
                            deserialize ((serialize x) ++ bin) = Some (x, bin)
  }.

Definition bool_serialize (a: bool) : list bool :=
  a :: nil.

Definition bool_deserialize (bin : list bool) : option (bool * list bool) :=
  match bin with
    | nil => None
    | h :: t => Some (h, t)
  end.

Lemma bool_serialize_reversible: forall (x: bool) (bin: list bool),
                                   bool_deserialize ((bool_serialize x) ++ bin) = Some (x, bin).
  intros; simpl.
  reflexivity.
Qed.

Instance Bool_Serializer: Serializer bool :=
  {
    serialize := bool_serialize;
    deserialize := bool_deserialize
  }.
intros; simpl.
reflexivity.
Qed.