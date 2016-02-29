Require Import List.
Require Import Arith.
Require Import Nat.

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

Fixpoint add_zeroes_rec (bin: list bool) length_left :=
  match length_left with
    | O => bin
    | S (n) => false :: (add_zeroes_rec bin n)
  end.

Definition add_zeroes bin len :=
  if ge_dec (length bin) len then
    bin
  else
    add_zeroes_rec bin len.

(* Fixpoint nat_to_binary_rec n := *)
(*   match n with *)
(*     | O => nil *)
(*     | _ => (modulo n 2 = 1) :: nat_to_binary_rec (div2 n) *)
(*   end. *)

(* Definition nat_to_binary n := *)
(*   rev (nat_to_binary_rec n). *)
