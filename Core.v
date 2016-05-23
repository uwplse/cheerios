Require Import Ascii.
Require Import List.
Require Import Cheerios.Binary.

Class Serializer A :=
  {
    serialize: A -> (list bool);
    deserialize: list bool -> option (A * list bool);
    deserialize_preserves_input: forall (x: A) (bin: list bool),
                            deserialize ((serialize x) ++ bin) = Some (x, bin)
  }.

Lemma Serialize_reversible:
  forall (A: Type) (serializer: Serializer A) (x: A),
    deserialize (serialize x) = Some(x, nil).
Proof.
  intros.
  rewrite <- deserialize_preserves_input.
  rewrite app_nil_r. reflexivity.
Qed.

Definition bool_serialize (a: bool) : list bool :=
  a :: nil.

Definition bool_deserialize (bin : list bool) : option (bool * list bool) :=
  match bin with
    | nil => None
    | h :: t => Some (h, t)
  end.

Lemma bool_deserialize_preserves_input: forall (x: bool) (bin: list bool),
                                   bool_deserialize ((bool_serialize x) ++ bin) = Some (x, bin).
Proof.
  intros; simpl.
  reflexivity.
Qed.

Instance Bool_Serializer: Serializer bool :=
  {
    serialize := bool_serialize;
    deserialize := bool_deserialize;
    deserialize_preserves_input := bool_deserialize_preserves_input
  }.

Instance Nat_Serializer : Serializer nat :=
  {
    serialize := uleb128_encode;
    deserialize := uleb128_decode;
    deserialize_preserves_input := uleb128_decode_encode
  }.

Definition ascii_serialize (a : ascii) : list bool :=
  serialize (nat_of_ascii a).

Definition ascii_deserialize (bin : list bool) : option (ascii * list bool) :=
  match deserialize bin with
    | None => None
    | Some (n, rest) => Some (ascii_of_nat n, rest)
  end.

Lemma ascii_deserialize_preserves_input : forall a bin,
    ascii_deserialize (ascii_serialize a ++ bin) = Some (a, bin).
Proof.
  unfold ascii_deserialize, ascii_serialize.
  intros a bin.
  now rewrite deserialize_preserves_input, ascii_nat_embedding.
Qed.

Instance Ascii_Serializer : Serializer ascii :=
  {
    serialize := ascii_serialize;
    deserialize := ascii_deserialize;
    deserialize_preserves_input := ascii_deserialize_preserves_input
  }.