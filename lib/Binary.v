Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Nat.
Require Import Omega.
Require Import StructTactics.

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