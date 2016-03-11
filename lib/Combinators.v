Require Import StructTactics.
Require Import List.
Require Import Types.

Section combinators.
  Variable A : Type.
  Variable sA : Serializer A.

  Definition option_serialize (o: option A) :=
    match o with
    | None => serialize false
    | Some t => serialize true ++ serialize t
    end.

  Definition option_deserialize (bin: list bool) : option (option A * list bool) :=
    match deserialize bin with
    | None => None
    | Some (b, rest) =>
    match b with
    | false => Some (None, rest)
    | true =>
    match deserialize rest with
    | None => None
    | Some (t, rest) =>
      Some (Some t, rest)
    end
    end
    end.

  Lemma option_serialize_reversible :
    forall (o: option A) (bin: list bool),
      option_deserialize (option_serialize o ++ bin) = Some (o, bin).
  Proof.
    unfold option_deserialize, option_serialize.
    intros o bin.
    destruct o; simpl; auto.
    now rewrite Serialize_reversible.
  Qed.

  (* Global here means "redeclare this instance outside the section."
     If you leave this off, then the instance must be manually re-declared. *)
  Global Instance Option_Serializer : Serializer (option A) :=
    {
      serialize := option_serialize;
      deserialize := option_deserialize;
      Serialize_reversible := option_serialize_reversible
    }.

  Variable B : Type.
  Variable sB : Serializer B.

  Definition pair_serialize (p: A*B) :=
    let (a, b) := p in
    (serialize a) ++ (serialize b).

  Definition pair_deserialize (bin: list bool) : option ((A * B) * list bool) :=
    match deserialize bin with
    | None => None
    | Some (a, rest) =>
    match deserialize rest with
    | None => None
    | Some (b, remainder) =>
      Some ((a, b), remainder)
    end
    end.

  Lemma pair_serialize_reversible :
    forall (p: A * B) (bin: list bool),
      pair_deserialize (pair_serialize p ++ bin) = Some (p, bin).
  Proof.
    intros.
    unfold pair_serialize.
    break_match.
    unfold pair_deserialize.
    rewrite app_assoc_reverse.
    now repeat rewrite Serialize_reversible.
  Qed.

  Global Instance Pair_Serializer : Serializer (A * B) :=
    {
      serialize := pair_serialize;
      deserialize := pair_deserialize;
      Serialize_reversible := pair_serialize_reversible
    }.

  Variable C : Type.
  Variable sC : Serializer C.

  Definition triple_serialize (t: A*B*C) :=
    let (p, c) := t in
    let (a, b) := p in
    (serialize a) ++ (serialize b) ++ (serialize c).

  Definition triple_deserialize (bin: list bool): option ((A*B*C) * list bool) :=
    match deserialize bin with
    | None => None
    | Some (a, rest) =>
    match deserialize rest with
    | None => None
    | Some (b, rest) =>
    match deserialize rest with
    | None => None
    | Some (c, remainder) =>
      Some ((a, b, c), remainder)
    end
    end
    end.

  Lemma triple_serialize_reversible :
    forall (t: A * B * C) (bin: list bool),
      triple_deserialize (triple_serialize t ++ bin) = Some (t, bin).
  Proof.
    intros.
    unfold triple_serialize.
    repeat break_match.
    unfold triple_deserialize.
    repeat rewrite app_assoc_reverse.
    now repeat rewrite Serialize_reversible.
  Qed.

  Global Instance Triple_Serializer : Serializer (A * B * C) :=
    {
      serialize := triple_serialize;
      deserialize := triple_deserialize;
      Serialize_reversible := triple_serialize_reversible
    }.

  Fixpoint list_serialize_rec (ts: list A) :=
    match ts with
    | nil => nil
    | hd :: ts => (serialize hd) ++ (list_serialize_rec ts)
    end.

  Definition list_serialize (ts: list A) :=
    serialize (length ts) ++ (list_serialize_rec ts).

  Fixpoint list_deserialize_rec (count: nat) (bin: list bool) : option (list A * list bool) :=
    match count with
      | 0 => Some (nil, bin)
      | S n =>
    match deserialize bin with
      | None => None
      | Some (t, rest) =>
    match list_deserialize_rec n rest with
      | None => None
      | Some (elements, rest) => Some ((t :: elements), rest)
    end
    end
    end.

  Definition list_deserialize (bin: list bool) : option (list A * list bool) :=
    match deserialize bin with
    | None => None
    | Some (count, rest) =>
      list_deserialize_rec count rest
    end.

  Lemma list_serialize_reversible :
    forall (ts: list A) (bin: list bool),
      list_deserialize (list_serialize ts ++ bin) = Some (ts, bin).
  Proof.
    unfold list_deserialize, list_serialize.
    intros ts bin.
    rewrite app_assoc_reverse.
    rewrite Serialize_reversible.
    induction ts; auto.
    simpl.
    rewrite app_assoc_reverse.
    rewrite Serialize_reversible.
    now rewrite IHts.
  Qed.

  Global Instance List_Serializer : Serializer (list A) :=
    {
      serialize := list_serialize;
      deserialize := list_deserialize;
      Serialize_reversible := list_serialize_reversible
    }.

  Definition sum_serialize (x : A + B) : list bool :=
    match x with
    | inl a => serialize true ++ serialize a
    | inr b => serialize false ++ serialize b
    end.

  Definition sum_deserialize (bin : list bool) : option ((A + B) * list bool) :=
    match deserialize(A:=bool) bin with None => None
    | Some (flag, bin) =>
      if flag
      then match deserialize bin with None => None
           | Some (a, bin) => Some (inl a, bin)
           end
      else match deserialize bin with None => None
           | Some (b, bin) => Some (inr b, bin)
           end
    end.

  Lemma sum_serialize_reversible :
    forall x bin,
      sum_deserialize (sum_serialize x ++ bin) = Some (x, bin).
  Proof.
    unfold sum_serialize, sum_deserialize.
    intros x bin.
    destruct x; rewrite app_assoc_reverse;
      now rewrite !Serialize_reversible.
  Qed.

  Global Instance Sum_Serializer : Serializer (A + B) :=
    {
      serialize := sum_serialize;
      deserialize := sum_deserialize;
      Serialize_reversible := sum_serialize_reversible
    }.
End combinators.
