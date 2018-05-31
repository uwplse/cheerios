Require Import Cheerios.ByteDecidable.
Require Import Cheerios.Types.

Require Import List.

Import ListNotations.

Inductive MsgPack :=
| Nil
| Bool : bool -> MsgPack
| UInt8 : byte -> MsgPack
| Str8 : list byte -> MsgPack
| Map : list (MsgPack * MsgPack) -> MsgPack.

Fixpoint unflatten_assoc_list' (l : list MsgPack) acc :=
  match l with
  | x :: y :: l => unflatten_assoc_list' l ((x, y) :: acc)
  | _ => List.rev acc
  end.

Definition unflatten_assoc_list l :=
  unflatten_assoc_list' l [].

Inductive MsgPack_denote : list byte -> MsgPack ->  Prop :=
| Nil_denote : MsgPack_denote [xc0] Nil
| False_denote : MsgPack_denote [xc2] (Bool false)
| True_denote : MsgPack_denote [xc3] (Bool true)
| UInt8_denote : forall b, MsgPack_denote [xcc; b] (UInt8 b)
| Str8_denote: forall b str, length str = byte_to_nat b ->
                        MsgPack_denote ([xd9] ++ [b] ++ str) (Str8 str)
(* incomplete - needs additional conversion between bytes/nat *)
| Map_denote : forall bytes l assoc_l, MsgPack_list bytes l ->
                                  unflatten_assoc_list l = assoc_l ->
                                  MsgPack_denote bytes (Map assoc_l)
with
MsgPack_list : list byte -> list MsgPack -> Prop :=
| MsgPack_list_Nil : MsgPack_list [] []
| MsgPack_list_Cons : forall  bytes m bytes' l,
    MsgPack_denote bytes m ->
    MsgPack_list bytes' l ->
    MsgPack_list (bytes ++ bytes') (m :: l).
