Require Import StructTactics.
Require Import List.
Require Import Types.

Definition option_serialize
           {T: Type}
           {tSerializer: Serializer T}
           (o: option T) :=
  match o with
    | None => serialize false
    | Some t => serialize true ++ serialize t
  end.

Definition option_deserialize
           {T: Type}
           {tSerializer: Serializer T}
           (bin: list bool) : option (option T * list bool) :=
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
  forall {T: Type}
    {tSerializer: Serializer T}
    (o: option T) (bin: list bool),
    option_deserialize (option_serialize o ++ bin) = Some (o, bin).
Proof.
  unfold option_deserialize, option_serialize.
  intros T tSerializer o bin.
  destruct o; simpl; auto.
  now rewrite Serialize_reversible.
Qed.

Instance Option_Serializer :
  forall (T: Type)
    {tSerializer: Serializer T}, Serializer (option T) :=
  {
    serialize := option_serialize;
    deserialize := option_deserialize;
    Serialize_reversible := option_serialize_reversible
  }.

Definition pair_serialize
           {A B: Type}
           {aSerializer: Serializer A}
           {bSerializer: Serializer B}
           (p: A*B) :=
  let (a, b) := p in
  (serialize a) ++ (serialize b).

Definition pair_deserialize
           {A B: Type}
           {aSerializer: Serializer A}
           {bSerializer: Serializer B}
           (bin: list bool) : option ((A * B) * list bool) :=
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
  forall {A B: Type}
    {aSerializer: Serializer A}
    {bSerializer: Serializer B}
    (p: A * B) (bin: list bool),
    pair_deserialize (pair_serialize p ++ bin) = Some (p, bin).
Proof.
  intros.
  unfold pair_serialize.
  break_match.
  unfold pair_deserialize.
  rewrite app_assoc_reverse.
  now repeat rewrite Serialize_reversible.
Qed.

Instance Pair_Serializer :
  forall (A B: Type)
    {aSerializer: Serializer A}
    {bSerializer: Serializer B}, Serializer (A * B) :=
  {
    serialize := pair_serialize;
    deserialize := pair_deserialize;
    Serialize_reversible := pair_serialize_reversible
  }.

Definition triple_serialize
           {A B C: Type}
           {aSerializer: Serializer A}
           {bSerializer: Serializer B}
           {cSerializer: Serializer C}
           (t: A*B*C) :=
  let (p, c) := t in
  let (a, b) := p in
  (serialize a) ++ (serialize b) ++ (serialize c).

Definition triple_deserialize
           {A B C: Type}
           {aSerializer: Serializer A}
           {bSerializer: Serializer B}
           {cSerializer: Serializer C}
           (bin: list bool): option ((A*B*C) * list bool) :=
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
  forall {A B C: Type}
    {aSerializer: Serializer A}
    {bSerializer: Serializer B}
    {cSerializer: Serializer C}
    (t: A * B * C) (bin: list bool),
    triple_deserialize (triple_serialize t ++ bin) = Some (t, bin).
Proof.
  intros.
  unfold triple_serialize.
  repeat break_match.
  unfold triple_deserialize.
  repeat rewrite app_assoc_reverse.
  now repeat rewrite Serialize_reversible.
Qed.

Instance Triple_Serializer :
  forall (A B C: Type)
    {aSerializer: Serializer A}
    {bSerializer: Serializer B}
    {cSerializer: Serializer C}, Serializer (A * B * C) :=
  {
    serialize := triple_serialize;
    deserialize := triple_deserialize;
    Serialize_reversible := triple_serialize_reversible
  }.

Fixpoint list_serialize_rec
         {T: Type}
         {tSerializer: Serializer T}
         (ts: list T) := 
  match ts with
    | nil => nil
    | hd :: ts => (serialize hd) ++ (list_serialize_rec ts)
  end.

Definition list_serialize
           {T: Type}
           {tSerializer: Serializer T}
           (ts: list T) :=
  serialize (length ts) ++ (list_serialize_rec ts).

Fixpoint list_deserialize_rec
         {T: Type}
         {tSerializer: Serializer T}
         (count: nat) (bin: list bool) :=
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

Definition list_deserialize
           {T: Type}
           {tSerializer: Serializer T}
           (bin: list bool) : option (list T * list bool) :=
  match deserialize bin with
    | None => None
    | Some (count, rest) =>
      list_deserialize_rec count rest
  end.

Lemma list_serialize_reversible :
  forall {T: Type}
    {tSerializer: Serializer T}
    (ts: list T) (bin: list bool),
    list_deserialize (list_serialize ts ++ bin) = Some (ts, bin).
Proof.
  unfold list_deserialize, list_serialize.
  intros T tSerializer ts bin.
  rewrite app_assoc_reverse.
  rewrite Serialize_reversible.
  induction ts; auto.
  simpl.
  rewrite app_assoc_reverse.
  rewrite Serialize_reversible.
  now rewrite IHts.
Qed.

Instance List_Serializer :
  forall (T: Type)
    {tSerializer: Serializer T},
    Serializer (list T) :=
  {
    serialize := list_serialize;
    deserialize := list_deserialize;
    Serialize_reversible := list_serialize_reversible
  }.