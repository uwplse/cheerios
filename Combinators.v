Require Import List.
Import ListNotations.
Require Vector String.

Require Import Cheerios.Core.
Require Import Cheerios.BasicSerializers.
Require Import Cheerios.DeserializerMonad.
Import DeserializerNotations.
Require Import Cheerios.Tactics.

(* These functions are either missing obvious implicits, or have
   implicit arguments that are not marked "maximally inserted", which
   means they cannot easily be used with map or fmap. *)
Arguments Some {_} _.
Arguments cons {_} _ _.
Arguments option_map {_ _} _ _.
Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.

Section combinators.

  (* This section gives instances for various type constructors, including pairs
    and lists. *)
  Variables A B : Type.
  Variable sA : Serializer A.
  Variable sB : Serializer B.

  Definition option_serialize (x : option A) : list bool :=
    match x with
    | Some a => serialize true ++ serialize a
    | None => serialize false
    end.

  Definition option_deserialize : deserializer (option A) :=
    b <- deserialize ;;
    match b with
    | true => Some <$> deserialize
    | false => ret None
    end.

  Lemma option_serialize_deserialize_id :
    serialize_deserialize_id_spec option_serialize option_deserialize.
  Proof.
    unfold option_serialize, option_deserialize.
    destruct a; serialize_deserialize_id_crush.
  Qed.

  Global Instance option_Serializer : Serializer (option A) :=
    {| serialize := option_serialize;
        deserialize := option_deserialize;
        serialize_deserialize_id := option_serialize_deserialize_id
    |}.

  Definition pair_serialize (x : A * B) : list bool :=
    let (a, b) := x in serialize a ++ serialize b.

  Definition pair_deserialize : deserializer (A * B) :=
    liftD2 pair.

  Lemma pair_serialize_deserialize_id :
    serialize_deserialize_id_spec pair_serialize pair_deserialize.
  Proof.
    unfold pair_serialize, pair_deserialize.
    destruct a; serialize_deserialize_id_crush.
  Qed.

  Global Instance pair_Serializer : Serializer (A * B) :=
    {| serialize := pair_serialize;
        deserialize := pair_deserialize;
        serialize_deserialize_id := pair_serialize_deserialize_id
    |}.


  Definition sum_serialize (x : A + B) : list bool :=
    match x with
    | inl a => serialize true ++ serialize a
    | inr b => serialize false ++ serialize b
    end.

  Definition sum_deserialize : deserializer (A + B) :=
    b <- deserialize ;;
    match b with
    | true => inl <$> deserialize
    | false => inr <$> deserialize
    end.

  Lemma sum_serialize_deserialize_id :
    serialize_deserialize_id_spec sum_serialize sum_deserialize.
  Proof.
    unfold sum_serialize, sum_deserialize.
    destruct a; serialize_deserialize_id_crush.
  Qed.

  Global Instance sum_Serializer : Serializer (A + B) :=
    {| serialize := sum_serialize;
        deserialize := sum_deserialize;
        serialize_deserialize_id := sum_serialize_deserialize_id
    |}.


  Fixpoint list_serialize_rec (l : list A) : list bool :=
    match l with
    | [] => []
    | a :: l' => serialize a ++ list_serialize_rec l'
    end.

  Definition list_serialize (l : list A) : list bool :=
    serialize (length l) ++ list_serialize_rec l.

  Fixpoint list_deserialize_rec (n : nat) : deserializer (list A) :=
    match n with
    | 0 => ret []
    | S n' => cons <$> deserialize <*> list_deserialize_rec n'
    end.

  Definition list_deserialize : deserializer (list A) :=
    deserialize >>= list_deserialize_rec.

  Lemma list_serialize_deserialize_id_rec :
    forall l bin, list_deserialize_rec (length l) (list_serialize_rec l ++ bin) = Some (l, bin).
  Proof.
    induction l; simpl; serialize_deserialize_id_crush.
    now rewrite IHl.
  Qed.

  Lemma list_serialize_deserialize_id :
    serialize_deserialize_id_spec list_serialize list_deserialize.
  Proof.
    unfold list_serialize, list_deserialize.
    serialize_deserialize_id_crush.
    apply list_serialize_deserialize_id_rec.
  Qed.

  Global Instance list_Serializer : Serializer (list A) :=
    {| serialize := list_serialize;
        deserialize := list_deserialize;
        serialize_deserialize_id := list_serialize_deserialize_id
    |}.

  Fixpoint vector_serialize {n} (v : Vector.t A n) : list bool :=
    match v with
    | Vector.nil => []
    | Vector.cons a v' => serialize a ++ vector_serialize v'
    end.

  Fixpoint vector_deserialize {n} : deserializer (Vector.t A n) :=
    match n as n0 return deserializer (Vector.t A n0) with
    | 0 => ret Vector.nil
    | S n' => a <- deserialize ;; v <- vector_deserialize ;; ret (Vector.cons a v)
    end.

  Lemma vector_serialize_deserialize_id :
    forall n, serialize_deserialize_id_spec vector_serialize (@vector_deserialize n).
  Proof.
    induction n; intros.
    - destruct a using Vector.case0. auto.
    - destruct a using Vector.caseS'.
      simpl.
      serialize_deserialize_id_crush.
      now rewrite IHn.
  Qed.

  Global Instance vector_Serializer n : Serializer (Vector.t A n) :=
    {| serialize := vector_serialize;
        deserialize := vector_deserialize;
        serialize_deserialize_id := vector_serialize_deserialize_id n
    |}.

End combinators.


(* This has to go here because it depends on having a serializer for
   lists available. *)

Fixpoint string_to_list s :=
  match s with
  | String.EmptyString => nil
  | String.String c s' => c :: (string_to_list s')
  end.

Fixpoint list_to_string l :=
  match l with
  | nil => String.EmptyString
  | h::l' => String.String h (list_to_string l')
  end.

Lemma string_to_list_to_string :
  forall s, list_to_string (string_to_list s) = s.
Proof.
  induction s; auto; simpl.
  now rewrite IHs.
Qed.

Definition string_serialize (s : String.string) :=
  serialize (string_to_list s).

Definition string_deserialize : deserializer String.string :=
  list_to_string <$> deserialize.

Lemma string_serialize_deserialize_id :
  serialize_deserialize_id_spec string_serialize string_deserialize.
Proof.
  unfold string_deserialize, string_serialize.
  serialize_deserialize_id_crush.
  now rewrite string_to_list_to_string.
Qed.

Instance string_Serializer : Serializer String.string :=
  {| serialize := string_serialize;
     deserialize := string_deserialize;
     serialize_deserialize_id := string_serialize_deserialize_id
  |}.


