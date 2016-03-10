Require Import Ascii.
Require Import List.
Require Import Binary.

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
Proof.
  intros; simpl.
  reflexivity.
Qed.

Instance Bool_Serializer: Serializer bool :=
  {
    serialize := bool_serialize;
    deserialize := bool_deserialize;
    Serialize_reversible := bool_serialize_reversible
  }.

Definition nat_serialize (n : nat) : list bool :=
  let bin := nat_to_binary n
  in nat_to_unary (length bin) ++ bin.

Definition nat_deserialize (bin : list bool) : option (nat * list bool) :=
  match unary_to_nat bin with None => None
  | Some (n, bin) =>
  match take n bin with None => None
  | Some (bin_n, bin) =>
    Some (binary_to_nat bin_n, bin)
  end
  end.

Lemma nat_serialize_reversible : forall n bin,
    nat_deserialize (nat_serialize n ++ bin) = Some (n, bin).
Proof.
  unfold nat_deserialize, nat_serialize.
  intros n bin.
  now rewrite app_assoc_reverse, nat_to_unary_to_nat, take_app, binary_to_nat_to_binary.
Qed.

Instance Nat_Serializer : Serializer nat :=
  {
    serialize := nat_serialize;
    deserialize := nat_deserialize;
    Serialize_reversible := nat_serialize_reversible
  }.

Definition ascii_serialize (a : ascii) : list bool :=
  serialize (nat_of_ascii a).

Definition ascii_deserialize (bin : list bool) : option (ascii * list bool) :=
  match deserialize bin with
    | None => None
    | Some (n, rest) => Some (ascii_of_nat n, rest)
  end.

Lemma ascii_serialize_reversible : forall a bin,
    ascii_deserialize (ascii_serialize a ++ bin) = Some (a, bin).
Proof.
  unfold ascii_deserialize, ascii_serialize.
  intros a bin.
  now rewrite Serialize_reversible, ascii_nat_embedding.
Qed.

Instance Ascii_Serializer : Serializer ascii :=
  {
    serialize := ascii_serialize;
    deserialize := ascii_deserialize;
    Serialize_reversible := ascii_serialize_reversible
  }.