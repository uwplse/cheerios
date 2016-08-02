Require Import List ZArith.
Import ListNotations.
Require Vector String.

From Cheerios Require Import Monoid Core BasicSerializers DeserializerMonad Tactics StringUtils.
Import DeserializerNotations.

(* These functions are either missing obvious implicits, or have
   implicit arguments that are not marked "maximally inserted", which
   means they cannot easily be used with map or fmap. *)
Arguments Some {_} _.
Arguments cons {_} _ _.
Arguments option_map {_ _} _ _.
Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.

Section bin.

Variable bin : Type.
Context {mbin : Monoid bin}.

Context {sbool : Serializer bin bool}.
Context {spos : Serializer bin positive}.

Section combinators.

  (* This section gives instances for various type constructors, including pairs
    and lists. *)
  Variables A B : Type.
  Variable sA : Serializer bin A.
  Variable sB : Serializer bin B.

  Definition option_serialize (x : option A) : bin :=
    match x with
    | Some a => serialize true +++ serialize a
    | None => serialize false
    end.

  Definition option_deserialize : deserializer bin (option A) :=
    b <- deserialize ;;
    match b with
    | true => Some <$> deserialize
    | false => ret None
    end.

  Lemma option_serialize_deserialize_id :
    serialize_deserialize_id_spec option_serialize option_deserialize.
  Proof.
    unfold option_serialize, option_deserialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance option_Serializer : Serializer bin (option A) :=
    {| serialize := option_serialize;
        deserialize := option_deserialize;
        serialize_deserialize_id := option_serialize_deserialize_id
    |}.

  Definition pair_serialize (x : A * B) : bin :=
    let (a, b) := x in serialize a +++ serialize b.

  Definition pair_deserialize : deserializer bin (A * B) :=
    liftD2 pair.

  Lemma pair_serialize_deserialize_id :
    serialize_deserialize_id_spec pair_serialize pair_deserialize.
  Proof.
    unfold pair_serialize, pair_deserialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance pair_Serializer : Serializer bin (A * B) :=
    {| serialize := pair_serialize;
        deserialize := pair_deserialize;
        serialize_deserialize_id := pair_serialize_deserialize_id
    |}.


  Definition sum_serialize (x : A + B) : bin :=
    match x with
    | inl a => serialize true +++ serialize a
    | inr b => serialize false +++ serialize b
    end.

  Definition sum_deserialize : deserializer bin (A + B) :=
    b <- deserialize ;;
    match b with
    | true => inl <$> deserialize
    | false => inr <$> deserialize
    end.

  Lemma sum_serialize_deserialize_id :
    serialize_deserialize_id_spec sum_serialize sum_deserialize.
  Proof.
    unfold sum_serialize, sum_deserialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance sum_Serializer : Serializer bin (A + B) :=
    {| serialize := sum_serialize;
        deserialize := sum_deserialize;
        serialize_deserialize_id := sum_serialize_deserialize_id
    |}.


  Fixpoint list_serialize_rec (l : list A) : bin :=
    match l with
    | [] => mempty
    | a :: l' => serialize a +++ list_serialize_rec l'
    end.

  Definition list_serialize (l : list A) : bin :=
    serialize (length l) +++ list_serialize_rec l.

  Fixpoint list_deserialize_rec (n : nat) : deserializer bin (list A) :=
    match n with
    | 0 => ret []
    | S n' => cons <$> deserialize <*> list_deserialize_rec n'
    end.

  Definition list_deserialize : deserializer bin (list A) :=
    deserialize >>= list_deserialize_rec.

  Lemma list_serialize_deserialize_id_rec :
    forall l bin, list_deserialize_rec (length l) (list_serialize_rec l +++ bin) = Some (l, bin).
  Proof.
    induction l; simpl; cheerios_crush.
    now rewrite IHl.
  Qed.

  Lemma list_serialize_deserialize_id :
    serialize_deserialize_id_spec list_serialize list_deserialize.
  Proof.
    unfold list_serialize, list_deserialize.
    cheerios_crush.
    apply list_serialize_deserialize_id_rec.
  Qed.

  Global Instance list_Serializer : Serializer bin (list A) :=
    {| serialize := list_serialize;
       deserialize := list_deserialize;
       serialize_deserialize_id := list_serialize_deserialize_id
    |}.

  Fixpoint vector_serialize {n} (v : Vector.t A n) : bin :=
    match v with
    | Vector.nil => mempty
    | Vector.cons a v' => serialize a +++ vector_serialize v'
    end.

  Fixpoint vector_deserialize {n} : deserializer bin (Vector.t A n) :=
    match n as n0 return deserializer bin (Vector.t A n0) with
    | 0 => ret Vector.nil
    | S n' => a <- deserialize ;; v <- vector_deserialize ;; ret (Vector.cons a v)
    end.

  Lemma vector_serialize_deserialize_id :
    forall n, serialize_deserialize_id_spec vector_serialize (@vector_deserialize n).
  Proof.
    induction n; intros.
    - destruct a using Vector.case0. simpl. rewrite mappend_mempty_l. auto.
    - destruct a using Vector.caseS'.
      simpl.
      cheerios_crush.
      now rewrite IHn.
  Qed.

  Global Instance vector_Serializer n : Serializer bin (Vector.t A n) :=
    {| serialize := vector_serialize;
        deserialize := vector_deserialize;
        serialize_deserialize_id := vector_serialize_deserialize_id n
    |}.
End combinators.

Context {sascii : Serializer bin Ascii.ascii}.


(* This has to go here because it depends on having a serializer for
   lists available. *)

Definition string_serialize (s : String.string) :=
  serialize (string_to_list s).

Definition string_deserialize : deserializer bin String.string :=
  list_to_string <$> deserialize.

Lemma string_serialize_deserialize_id :
  serialize_deserialize_id_spec string_serialize string_deserialize.
Proof.
  unfold string_deserialize, string_serialize.
  cheerios_crush.
  now rewrite string_to_list_to_string.
Qed.

Global Instance string_Serializer : Serializer bin String.string :=
  {| serialize := string_serialize;
     deserialize := string_deserialize;
     serialize_deserialize_id := string_serialize_deserialize_id
  |}.


End bin.