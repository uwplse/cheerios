Require Import List ZArith.
Import ListNotations.

From StructTact Require Import StructTactics Fin.
Require Fin Ascii.

Require Import Cheerios.Core.
Require Import Cheerios.Tactics.
Require Import Cheerios.DeserializerMonad.
Import DeserializerNotations.

Definition bool_serialize (b : bool) : list bool := [b].

Definition bool_deserialize : deserializer bool :=
  l <- get ;;
  match l with
  | [] => fail
  | b :: l' => put l' ;; ret b
  end.

Lemma bool_serialize_deserialize_id :
  serialize_deserialize_id_spec bool_serialize bool_deserialize.
Proof.
  destruct a; auto.
Qed.

Instance bool_Serializer : Serializer bool :=
  {| serialize := bool_serialize;
     deserialize := bool_deserialize;
     serialize_deserialize_id := bool_serialize_deserialize_id
  |}.


(* This is about 2x less space-efficient than necessary, since it outputs two
   bits for every "bit" in the input, but it's very easy to verify. *)
Fixpoint positive_serialize (p : positive) : list bool :=
  match p with
  | xI p' => serialize true ++ serialize true ++ positive_serialize p'
  | xO p' => serialize true ++ serialize false ++ positive_serialize p'
  | xH => serialize false
  end.

(* This has to be implemented directly on the implementation of Deserializer.t
   because it performs recursion on the underlying list of bits. *)
Fixpoint positive_deserialize (l : list bool) : option (positive * list bool) :=
  match l with
  | [] => None
  | continue :: l' =>
    if continue
    then match l' with
         | [] => None
         | bit :: l' => match positive_deserialize l' with None => None
                       | Some (p, l') => Some ((if bit then xI else xO) p, l')
                       end
         end
    else Some (xH, l')
  end.

Lemma positive_serialize_deserialize_id :
  forall p bin, positive_deserialize (positive_serialize p ++ bin) = Some (p, bin).
Proof.
  induction p; simpl; intros; auto; rewrite IHp; auto.
Qed.

Instance positive_Serializer : Serializer positive :=
  {| serialize := positive_serialize;
     deserialize := positive_deserialize;
     serialize_deserialize_id := positive_serialize_deserialize_id
  |}.

(* This is the first example of a "typical" serializer: it combines more
   primitive serializers (in this case, just for bool and positive) together in
   order to serialize a Z. *)
Definition Z_serialize (z : Z) : list bool :=
  match z with
  | Z0 => serialize false
  | Zpos p => serialize true ++ serialize true ++ serialize p
  | Zneg p => serialize true ++ serialize false ++ serialize p
  end.

Definition Z_deserialize : deserializer Z :=
  tag <- deserialize ;;
  match tag with
  | true => sign <- deserialize ;;
           (match sign with true => Zpos | false => Zneg end) <$> deserialize
  | false => ret Z0
  end.

(* This proof is typical for serializing an algebraic datatype. Unfold the
   serializer and deserializer, then do a case analysis and call
   serialize_deserialize_id_crush. *)
Lemma Z_serialize_deserialize_id :
  serialize_deserialize_id_spec Z_serialize Z_deserialize.
Proof.
  unfold Z_serialize, Z_deserialize.
  destruct a; serialize_deserialize_id_crush.
Qed.

Instance Z_Serializer : Serializer Z :=
  {| serialize := Z_serialize;
     deserialize := Z_deserialize;
     serialize_deserialize_id := Z_serialize_deserialize_id
  |}.


Definition N_serialize (n : N) : list bool :=
  match n with
  | N0 => serialize false
  | Npos p => serialize true ++ serialize p
  end.

Definition N_deserialize : deserializer N :=
  tag <- deserialize ;;
  match tag with
  | false => ret N0
  | true => Npos <$> deserialize
  end.

Lemma N_serialize_deserialize_id :
  serialize_deserialize_id_spec N_serialize N_deserialize.
Proof.
  unfold N_serialize, N_deserialize.
  destruct a; serialize_deserialize_id_crush.
Qed.

Instance N_Serializer : Serializer N :=
  {| serialize := N_serialize;
     deserialize := N_deserialize;
     serialize_deserialize_id := N_serialize_deserialize_id
  |}.


(* The other main way to define a serializer is to use an isomorphism to another
   type that is already serializable. *)
Definition nat_serialize (n : nat) : list bool := serialize (N.of_nat n).

Definition nat_deserialize : deserializer nat := N.to_nat <$> deserialize.

(* This proof is typical for serializers defined by converting to and from a
   type that is already serializable. Unfold the serializer and deserializer,
   call serialize_deserialize_id_crush, and then use the proof that the
   conversion functions are inverses. *)
Lemma nat_serialize_deserialize_id :
  serialize_deserialize_id_spec nat_serialize nat_deserialize.
Proof.
  unfold nat_serialize, nat_deserialize.
  serialize_deserialize_id_crush.
  now rewrite Nnat.Nat2N.id.
Qed.

Instance nat_Serializer : Serializer nat :=
  {| serialize := nat_serialize;
     deserialize := nat_deserialize;
     serialize_deserialize_id := nat_serialize_deserialize_id
  |}.


(* Serializer for the standard library's Fin.t based on converting to nat. *)
Definition Fin_serialize {n} (x : Fin.t n) : list bool :=
  serialize (proj1_sig (Fin.to_nat x)).

Definition Fin_deserialize {n} : deserializer (Fin.t n) :=
  m <- deserialize ;;
    match Fin.of_nat m n with
    | inleft x => ret x
    | inright _ => fail
    end.

Lemma Fin_of_nat_to_nat:
  forall (n : nat) (a : Fin.t n), Fin.of_nat (proj1_sig (Fin.to_nat a)) n = inleft a.
Proof.
  induction a.
  - auto.
  - simpl. break_let. simpl in *.
    now rewrite IHa.
Qed.

Lemma Fin_serialize_deserialize_id n : serialize_deserialize_id_spec Fin_serialize (@Fin_deserialize n).
Proof.
  unfold Fin_serialize, Fin_deserialize.
  serialize_deserialize_id_crush.
  now rewrite Fin_of_nat_to_nat.
Qed.

Instance Fin_Serializer n : Serializer (Fin.t n) :=
  {| serialize := Fin_serialize;
     deserialize := Fin_deserialize;
     serialize_deserialize_id := Fin_serialize_deserialize_id n
  |}.


(* Serializer for StructTact's fin based on converting to nat. *)
Definition fin_serialize {n} (x : fin n) : list bool :=
  serialize (fin_to_nat x).

Definition fin_deserialize {n} : deserializer (fin n) :=
  m <- deserialize ;;
    match fin_of_nat m n with
    | inleft x => ret x
    | inright _ => fail
    end.

Lemma fin_serialize_deserialize_id n : serialize_deserialize_id_spec fin_serialize (@fin_deserialize n).
Proof.
  unfold fin_serialize, fin_deserialize.
  serialize_deserialize_id_crush.
  now rewrite fin_of_nat_fin_to_nat.
Qed.

Instance fin_Serializer n : Serializer (fin n) :=
  {| serialize := fin_serialize;
     deserialize := fin_deserialize;
     serialize_deserialize_id := fin_serialize_deserialize_id n
  |}.


Definition ascii_serialize (a : Ascii.ascii) : list bool :=
  serialize (Ascii.nat_of_ascii a).

Definition ascii_deserialize : deserializer Ascii.ascii :=
  Ascii.ascii_of_nat <$> deserialize.

Lemma ascii_serialize_deserialize_id :
  serialize_deserialize_id_spec ascii_serialize ascii_deserialize.
Proof.
  unfold ascii_deserialize, ascii_serialize.
  serialize_deserialize_id_crush.
  now rewrite Ascii.ascii_nat_embedding.
Qed.

Instance ascii_Serializer : Serializer Ascii.ascii :=
  {| serialize := ascii_serialize;
     deserialize := ascii_deserialize;
     serialize_deserialize_id := ascii_serialize_deserialize_id
  |}.
