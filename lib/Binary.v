Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.
Require Import StructTact.StructTactics.

Fixpoint take_rec (acc: list bool) c xs :=
  match c with
    | O => Some (rev acc, xs)
    | S n =>
      match xs with
        | nil => None
        | x::xs => take_rec (x :: acc) n xs
      end
  end.

Definition take c xs :=
  take_rec nil c xs.

Lemma take_rec_app :
  forall xs ys acc,
    take_rec acc (length xs) (xs ++ ys) = Some (rev acc ++ xs, ys).
Proof.
  induction xs; simpl; intros ys acc.
  - now rewrite app_nil_r.
  - rewrite IHxs.
    simpl.
    now rewrite app_assoc_reverse.
Qed.

Lemma take_app :
  forall xs ys,
    take (length xs) (xs ++ ys) = Some (xs, ys).
Proof.
  unfold take.
  intros xs ys.
  now rewrite take_rec_app.
Qed.

Fixpoint nat_to_unary n : list bool :=
  match n with
  | 0 => [false]
  | S n' => true :: nat_to_unary n'
  end.

Fixpoint unary_to_nat (bin : list bool) : option (nat * list bool) :=
  match bin with
  | [] => None
  | b :: bin' => if b
                then match unary_to_nat bin' with
                     | None => None
                     | Some (n, rest) => Some (S n, rest)
                     end
                else Some (0, bin')
  end.

Lemma nat_to_unary_to_nat :
  forall n bin,
    unary_to_nat (nat_to_unary n ++ bin) = Some (n, bin).
Proof.
  induction n as [|n' IHn']; intros bin.
  - reflexivity.
  - simpl. now rewrite IHn'.
Qed.

Fixpoint nat_to_binary_rec fuel n :=
  match fuel with
    | 0 => nil
    | S fuel =>
  match n with
    | O => nil
    | _ => (Nat.odd n) :: nat_to_binary_rec fuel (div2 n)
  end
  end.

Definition nat_to_binary n :=
  rev (nat_to_binary_rec n n).

Fixpoint binary_to_nat_rec bin :=
  match bin with
    | nil => 0
    | hd::bin =>
      Nat.b2n hd + 2 * (binary_to_nat_rec bin)
  end.

Definition binary_to_nat bin :=
  binary_to_nat_rec (List.rev bin).

Lemma binary_to_nat_to_binary_rec :
  forall fuel n,
    n <= fuel ->
    binary_to_nat_rec (nat_to_binary_rec fuel n) = n.
Proof.
  induction fuel; intros n Hfuel.
  - simpl. omega.
  - cbn [nat_to_binary_rec].
    destruct n; auto.
    cbn [binary_to_nat_rec].
    rewrite IHfuel by eauto using le_trans, Nat.le_div2 with *.
    now rewrite plus_comm, <- Nat.div2_odd.
Qed.

Lemma binary_to_nat_to_binary :
  forall n,
    binary_to_nat (nat_to_binary n) = n.
Proof.
  intros n.
  unfold binary_to_nat, nat_to_binary.
  rewrite rev_involutive.
  apply binary_to_nat_to_binary_rec.
  apply le_refl.
Qed.

Fixpoint bits_of (n_bits : nat) (x : nat) : (list bool * nat) :=
  match n_bits with
  | 0 => ([], x)
  | S n_bits' => let (l,x') := bits_of n_bits' (Nat.div2 x)
                in (Nat.odd x :: l, x')
  end.

Lemma length_bits_of :
  forall n x l x', bits_of n x = (l, x') ->
              length l = n.
Proof.
  induction n; simpl; intros x l x' H.
  - find_inversion. auto.
  - break_let. apply IHn in Heqp.
    find_inversion. auto.
Qed.

Fixpoint uleb128_encode' fuel n : list bool :=
  let (byte, n') := bits_of 7 n
  in match n' with
     | 0 => false :: byte
     | S _ => true :: byte ++
             match fuel with
             | 0 => []
             | S fuel' => uleb128_encode' fuel' n'
             end
     end.
Definition uleb128_encode n := uleb128_encode' n n.

Fixpoint uleb128_decode (bin : list bool) : option (nat * list bool) :=
  match bin with
  | b_cont::b0::b1::b2::b3::b4::b5::b6::bin' =>
    let n := binary_to_nat_rec [b0;b1;b2;b3;b4;b5;b6]
    in if b_cont
       then match uleb128_decode bin' with None => None
            | Some (ans, bin'') => Some (n + 128 * ans, bin'')
            end
       else Some (n, bin')
  | _ => None
  end.

Lemma shiftr_div2_comm :
  forall b a,
    Nat.shiftr (Nat.div2 a) b = Nat.div2 (Nat.shiftr a b).
Proof.
  induction b; simpl; intros a; auto using f_equal.
Qed.

Lemma bits_of_x' :
  forall n x l x',
    bits_of n x = (l, x') ->
    x' = Nat.shiftr x n.
Proof.
  induction n; simpl; intros x l x' H.
  - now find_inversion.
  - break_let. apply IHn in Heqp. find_inversion. apply shiftr_div2_comm.
Qed.

Lemma mod2n_succ:
  forall n x : nat, Nat.b2n (Nat.odd x) + 2 * (Nat.div2 x mod 2 ^ n) = x mod 2 ^ S n.
Proof.
  intros n x.
  apply Nat.bits_inj.
  intro i.
  repeat rewrite <- Nat.land_ones.
  repeat rewrite Nat.land_spec.
  rewrite plus_comm.
  destruct i.
  + now rewrite Nat.testbit_0_r, Nat.ones_spec_low, Nat.bit0_odd, Bool.andb_true_r by omega.
  + rewrite Nat.testbit_succ_r, Nat.land_spec, Nat.div2_spec, Nat.shiftr_specif, plus_comm.
    f_equal.
    destruct (lt_dec i n).
    * now rewrite !Nat.ones_spec_low by omega.
    * now rewrite !Nat.ones_spec_high by omega.
Qed.

Lemma bits_of_l :
  forall n x l x',
    bits_of n x = (l, x') ->
    binary_to_nat_rec l = x mod (2 ^ n).
Proof.
  induction n; intros x l x' H.
  - simpl in *. now find_inversion.
  - cbn [bits_of] in *.
    break_let. apply IHn in Heqp.
    find_inversion.
    cbn [binary_to_nat_rec].
    rewrite Heqp.
    apply mod2n_succ.
Qed.

Lemma bits_of_reconstruct :
  forall n x l x',
    bits_of n x = (l, x') ->
    x = binary_to_nat_rec l + 2 ^ n * x'.
Proof.
  intros.
  find_copy_apply_lem_hyp bits_of_l.
  find_apply_lem_hyp bits_of_x'.
  subst.
  now rewrite Nat.shiftr_div_pow2, H0, plus_comm, <- Nat.div_mod
    by (apply Nat.pow_nonzero; congruence).
Qed.

Lemma uleb128_decode_encode' :
  forall fuel n bin,
    n <= fuel ->
    uleb128_decode (uleb128_encode' fuel n ++ bin) = Some (n, bin).
Proof.
  induction fuel as [|fuel' IHfuel']; intros n bin Hle.
  - destruct n.
    + reflexivity.
    + omega.
  - cbn [uleb128_encode'].
    break_let.
    find_copy_apply_lem_hyp length_bits_of.
    do 8 (destruct l; simpl in H; try omega).
    find_apply_lem_hyp bits_of_reconstruct.
    subst n.
    break_match; cbn [app uleb128_decode].
    + f_equal. f_equal. omega.
    + rewrite IHfuel'; auto.
      replace (2 ^ 7) with 128 in * by auto.
      omega.
Qed.

Lemma uleb128_decode_encode :
  forall n bin,
    uleb128_decode (uleb128_encode n ++ bin) = Some (n, bin).
Proof.
  unfold uleb128_encode.
  intros.
  apply uleb128_decode_encode'.
  auto.
Qed.
