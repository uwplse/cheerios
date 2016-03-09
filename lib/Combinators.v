Require Import StructTactics.
Require Import List.
Require Import Types.

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
           (bin: list bool) :=
  match (@deserialize A aSerializer bin) with
    | None => None
    | Some (a, rest) =>
  match (@deserialize B bSerializer rest) with (* Is there a better way to have coq figure this out? *)
    | None => None
    | Some (b, remainder) =>
      Some ((a, b), remainder)
  end
  end.

Instance Pair_Serializer: forall (A B: Type), Serializer (A * B) :=
  {
    serialize := pair_serialize;
    deserialize := pair_deserialize;
  }.


(* Check pair_deserialize. *)

(* Lemma pair_serialize_reversible: forall {A B: Type} *)
(*                                    {aSerializer: Serializer A} *)
(*                                    {bSerializer: Serializer B} *)
(*                                    (x: (A * B)) *)
(*                                    (bin: list bool), *)
(*                                    pair_deserialize ((pair_serialize x) ++ bin) = Some (x, bin). *)
(*   intros. *)
(*   destruct aSerializer. *)
(*   destruct bSerializer. *)
(*   unfold pair_serialize. *)
(*   break_match. *)
(*   unfold pair_deserialize. *)
(*   rewrite app_assoc_reverse. *)
(*   unfold Types.serialize. *)
(*   unfold Types.deserialize. *)
(*   rewrite Serialize_reversible. *)
(*   rewrite Serialize_reversible0. *)
(*   reflexivity. *)
(* Qed. *)