Require Import List ZArith.
Import ListNotations.

From Cheerios Require Import Monoid Core Tactics DeserializerMonad.
Import DeserializerNotations.

Definition bool_serialize (b : bool) : list bool := [b].

Definition bool_deserialize : deserializer (list bool) bool :=
  l <- get ;;
  match l with
  | [] => fail
  | b :: l' => put l' ;; ret b
  end%list.

Lemma bool_serialize_deserialize_id :
  serialize_deserialize_id_spec bool_serialize bool_deserialize.
Proof.
  destruct a; auto.
Qed.

Instance bool_Serializer : Serializer (list bool) bool :=
  {| serialize := bool_serialize;
     deserialize := bool_deserialize;
     serialize_deserialize_id := bool_serialize_deserialize_id
  |}.


(* This is about 2x less space-efficient than necessary, since it outputs two
   bits for every "bit" in the input, but it's very easy to verify. *)
Fixpoint positive_serialize (p : positive) : list bool :=
  match p with
  | xI p' => serialize true +++ serialize true +++ positive_serialize p'
  | xO p' => serialize true +++ serialize false +++ positive_serialize p'
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
  end%list.

Lemma positive_serialize_deserialize_id :
  forall p bin, positive_deserialize (positive_serialize p +++ bin) = Some (p, bin).
Proof.
  simpl.
  induction p; simpl; intros; auto; rewrite IHp; auto.
Qed.

Instance positive_Serializer : Serializer (list bool) positive :=
  {| serialize := positive_serialize;
     deserialize := positive_deserialize;
     serialize_deserialize_id := positive_serialize_deserialize_id
  |}.

Lemma fold_list_mappend : forall A (xs ys : list A), xs ++ ys = xs +++ ys.
Proof. auto. Qed.

Lemma serialize_deserialize_id_list_bool :
  forall A (sA : Serializer (list bool) A)
    (a : A) (bin : list bool),
    deserialize (serialize a ++ bin) = Some (a, bin).
Proof.
  intros.
  now rewrite fold_list_mappend, serialize_deserialize_id.
Qed.

Hint Rewrite
     fold_list_mappend
     @serialize_deserialize_id_list_bool
  : cheerios.
