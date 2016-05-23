Require Import StructTact.StructTactics.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import Cheerios.Core.
Require Import Cheerios.Combinators.

Fixpoint string_to_list s :=
  match s with
    | EmptyString => nil
    | String c s' => c :: (string_to_list s')
  end.

Fixpoint list_to_string l :=
  match l with
    | nil => EmptyString
    | h::l' => String h (list_to_string l')
  end.

Lemma string_to_list_to_string : forall s,
                                  list_to_string (string_to_list s) = s.
Proof.
  induction s; auto; simpl.
  now rewrite IHs.
Qed.

Definition string_serialize (s : string) :=
  serialize (string_to_list s).

Definition string_deserialize bin : option (string * list bool) :=
  match deserialize bin with
    | None => None
    | Some (cs, rest) => Some (list_to_string cs, rest)
  end.

Lemma string_deserialize_preserves_input : forall s bin,
    string_deserialize (string_serialize s ++ bin) = Some (s, bin).
Proof.
  unfold string_deserialize, string_serialize.
  intros s bin.
  rewrite deserialize_preserves_input.
  now rewrite string_to_list_to_string.
Qed.

Definition Z_to_nat (z : Z) : nat := 2 * (Z.abs_nat z) + Nat.b2n (0 <=? z)%Z.

Definition nat_to_Z (n : nat) : Z :=
  let abs := Z.of_nat (Nat.div2 n)
  in
  if Nat.odd n
  then abs
  else Z.opp abs.

Lemma odd_b2n :
  forall b, Nat.odd (Nat.b2n b) = b.
Proof.
  destruct b; auto.
Qed.

Lemma Z_to_nat_inverse :
  forall z, nat_to_Z (Z_to_nat z) = z.
Proof.
  unfold nat_to_Z, Z_to_nat.
  intros z.
  rewrite Nat.div2_div, plus_comm, Nat.add_b2n_double_div2, Zabs2Nat.id_abs.
  rewrite Nat.odd_add_mul_2, odd_b2n.
  break_if.
  - apply Z.leb_le in Heqb.
    now rewrite Z.abs_eq by omega.
  - apply Z.leb_gt in Heqb.
    destruct (Z.abs_spec z); intuition.
Qed.

Instance Z_Serializer : Serializer Z :=
  To_From_Serializer Nat_Serializer _ _ Z_to_nat_inverse.