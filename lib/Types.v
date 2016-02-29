Require Import List.

Class Serializer {A:Type}(serialize: A -> list bool)(deserialize: list bool -> option (A * list bool)) : Prop :=
  {
    serialize_reversible: forall x: A,
                            deserialize (serialize x) = Some (x, nil);
    deserialize_reversible: forall (b: list bool) (a: A),
                              deserialize b = Some (a, nil) ->
                              serialize a = b
  }.

Definition bool_serialize (a: bool) : list bool :=
  a :: nil.

Definition bool_deserialize (bin : list bool) : option (bool * list bool) :=
  match bin with
    | nil => None
    | h :: t => Some (h, t)
  end.

Instance Bool_Serializer: Serializer bool_serialize bool_deserialize.
split; simpl; intros.
- reflexivity.
- destruct b; inversion H; reflexivity.
Qed.