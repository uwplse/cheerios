Require Import List ZArith.
Import ListNotations.

From StructTact Require Import StructTactics Fin.
Require Fin Ascii String.

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
  serialize (Ascii.N_of_ascii a).

Definition ascii_deserialize : deserializer Ascii.ascii :=
  Ascii.ascii_of_N <$> deserialize.

Lemma ascii_serialize_deserialize_id :
  serialize_deserialize_id_spec ascii_serialize ascii_deserialize.
Proof.
  unfold ascii_deserialize, ascii_serialize.
  serialize_deserialize_id_crush.
  now rewrite Ascii.ascii_N_embedding.
Qed.

Instance ascii_Serializer : Serializer Ascii.ascii :=
  {| serialize := ascii_serialize;
     deserialize := ascii_deserialize;
     serialize_deserialize_id := ascii_serialize_deserialize_id
  |}.

Require Import mathcomp.ssreflect.ssreflect.

Theorem list_ind_cons2 :
 forall (B:Set) (P:list B -> Prop),
   P nil ->
   (forall x:B, P (x :: nil)) ->
   (forall (x1 x2:B) (l:list B), P l -> P (x1 :: x2 :: l)) ->
   forall l:list B, P l.
Proof.
move => B P P0 P1 Pr l; cut (P l /\ (forall x:B, P (x :: l))); first by intuition.
by elim: l; intuition.
Qed.

Lemma positive_deserialize_lt_length :
  forall l l' p,
    positive_deserialize l = Some (p, l') ->
    length l' < length l.
Proof.
elim/list_ind_cons2 => //=.
- case => //=.
  move => l' p H_eq.
  injection H_eq => H_eq_l H_eq_p.
  by rewrite -H_eq_l.
- case; case => l IH l' p H_eq.
  * destruct (positive_deserialize l) => //.
    break_let.
    find_injection.
    have IH' := IH l' p1 (eq_refl _).
    by auto with arith.
  * destruct (positive_deserialize l) => //.
    break_let.
    find_injection.
    have IH' := IH l' p1 (eq_refl _).
    by auto with arith.
  * find_injection.
    rewrite /=.
    by auto with arith.
  * find_injection.
    rewrite /=.
    by auto with arith.
Qed.

Lemma N_deserialize_lt_length :
  forall l l' n,
    N_deserialize l = Some (n, l') ->
    length l' < length l.
Proof.
move => l l' n.
rewrite /N_deserialize /bind /deserialize /= /bool_deserialize /bind /get /fmap /get /ret /= /bind.
case: l => //=.
case => l.
- case H_eq: (positive_deserialize l) => [p|] H_eq'; last by congruence.
  break_let.
  find_injection.
  have H_lt := positive_deserialize_lt_length _ _ _ H_eq.
  by auto with arith.
- move => H_eq.
  find_injection.
  by auto with arith.
Qed.

Lemma ascii_deserialize_lt_length :
  forall l l' c,
    ascii_deserialize l = Some (c, l') ->
    length l' < length l.
Proof.
move => l l' c.
rewrite /ascii_deserialize /bind /deserialize /= /fmap /get /bind /ret.
case H_eq: (N_deserialize l) => [n|] H_eq'; last by congruence.
break_let.
find_injection.
exact: N_deserialize_lt_length _ _ _ H_eq.
Qed.

Fixpoint string_serialize (s : String.string) : list bool :=
match s with
| String.EmptyString => serialize false
| String.String c s' => serialize true ++ ascii_serialize c ++ string_serialize s'
end.

Definition len_lt (l1 l2 : list bool) :=
  length l1 < length l2.

Theorem len_lt_well_founded : well_founded len_lt.
Proof.
 apply well_founded_lt_compat with (f := fun l => length l); auto.
Defined.

Definition string_deserialize_t (l : list bool) := option (String.string * list bool).

Definition string_deserialize_F l (string_deserialize_rec : forall l', len_lt l' l -> string_deserialize_t l') : string_deserialize_t l.
refine
(match l as l_eq return (l = l_eq -> _) with
| [] => fun _ => None
| false :: l' => fun _ => Some (String.EmptyString, l')
| true :: l' =>
  fun H_l_eq =>
  match ascii_deserialize l' as l_ad return (_ = l_ad -> _) with
  | None => fun _ => None
  | Some (c, l0) =>
    fun H_ad_eq =>
    match string_deserialize_rec l0 _ with
    | None => None
    | Some (s, l1) =>
      Some (String.String c s, l1)
    end
  end (refl_equal _)
end (refl_equal _)).
rewrite H_l_eq /= /len_lt /=.
apply ascii_deserialize_lt_length in H_ad_eq.
auto with arith.
Defined.

Definition string_deserialize : forall l, string_deserialize_t l :=
 Fix len_lt_well_founded string_deserialize_t string_deserialize_F.

Lemma string_deserialize_F_aux :
forall (x : list bool) (f g : forall y : list bool, len_lt y x -> string_deserialize_t y),
  (forall (y : list bool) (p : len_lt y x), f y p = g y p) -> string_deserialize_F x f = string_deserialize_F x g.
Proof.
case => //=.
rewrite /len_lt /=.
move => a l f g H_eq.
break_if => //.
rewrite /eq_ind_r /=.
Admitted.

Lemma string_serialize_deserialize_id :
  serialize_deserialize_id_spec string_serialize string_deserialize.
Proof.
unfold string_serialize, string_deserialize.
move => a bin.
rewrite Fix_eq /=; last exact: string_deserialize_F_aux.
rewrite -/(string_serialize _).
move: a bin.
elim => //= a s IH l.
rewrite -app_assoc.
rewrite ascii_serialize_deserialize_id.
have IH' := IH l.
rewrite -Fix_eq in IH'; last exact: string_deserialize_F_aux.
by rewrite IH'.
Qed.

Instance string_Serializer : Serializer String.string :=
  {| serialize := string_serialize;
     deserialize := string_deserialize;
     serialize_deserialize_id := string_serialize_deserialize_id
  |}.
