Require Import Cheerios.ByteDecidable.
Require Import Cheerios.Combinators.
Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Types.

(* Ensures (?) that any user of this will use the nat serializer we assume for
   the semanics below *)
Require Export Cheerios.ExtrOcamlCheeriosNatInt.

Require Import List.

Import ListNotations.
Import DeserializerNotations.

Inductive MsgPack :=
| Nil
| Bool : bool -> MsgPack
| UInt32 : nat -> MsgPack
| Str32 : list byte -> MsgPack
(* Map uses flattened assoc list to simplify serializer definition *)
| Map : list MsgPack -> MsgPack.


Fixpoint flatten_aux {A} (l : list (A * A)) acc :=
  match l with
  | [] => List.rev acc
  | (x, y) :: l => flatten_aux l (y :: x :: acc)
  end.

Definition flatten {A} (l : list (A * A)) : list A :=
  flatten_aux l [].

Fixpoint unflatten_aux {A} (l : list A) acc :=
  match l with
  | x :: y :: l => unflatten_aux l ((x, y) :: acc)
  | _ => List.rev acc
  end.

Definition unflatten {A} (l : list A) :=
  unflatten_aux l [].

Inductive MsgPack_denote : list byte -> MsgPack ->  Prop :=
| Nil_denote : MsgPack_denote [xc0] Nil
| False_denote : MsgPack_denote [xc2] (Bool false)
| True_denote : MsgPack_denote [xc3] (Bool true)
| UInt32_denote : forall bytes n,
    (* assumes nats are serialized as 32-bit ints *)
    (ByteListReader.unwrap deserialize) bytes = Some (n, []) ->
    MsgPack_denote (xce :: bytes) (UInt32 n)
| Str32_denote: forall bytes n str,
    (* assumes nats are serialized as 32-bit ints *)
    (ByteListReader.unwrap deserialize) bytes = Some (n, []) ->
    length str = n ->
    MsgPack_denote ([xd9] ++ bytes ++ str) (Str32 str)
| Map_denote : forall bytes n bytes' l,
    (* assumes nats are serialized as 32-bit ints *)
    (ByteListReader.unwrap deserialize) bytes = Some (n, []) ->
    length l = 2 * n ->
    MsgPack_list bytes l ->
    MsgPack_denote ([xdf] ++ bytes ++ bytes') (Map l)
with
MsgPack_list : list byte -> list MsgPack -> Prop :=
| MsgPack_list_Nil : MsgPack_list [] []
| MsgPack_list_Cons : forall  bytes m bytes' l,
    MsgPack_denote bytes m ->
    MsgPack_list bytes' l ->
    MsgPack_list (bytes ++ bytes') (m :: l).

(* list serializer that doesn't require a Serializer instance for A.
   to make recursive call to MsgPack_serialize for serializing Maps. *)
Fixpoint list_serialize_rec' {A} (s : A -> IOStreamWriter.t) (l : list A) :=
  match l with
  | [] => IOStreamWriter.empty
  | a :: l => s a +$+ list_serialize_rec' s l
  end.

Definition list_serialize' {A} s (l : list A) :=
  serialize (length l) +$+ list_serialize_rec' s l.

Fixpoint MsgPack_serialize (m : MsgPack) : IOStreamWriter.t :=
  let fix serialize_list_MsgPack (l : list MsgPack) : IOStreamWriter.t :=
      match l with
      | [] => IOStreamWriter.empty
      | m :: l =>
        MsgPack_serialize m +$+ serialize_list_MsgPack l
      end
  in
  match m with
  | Nil => serialize xc0
  | Bool false => serialize xc2
  | Bool true => serialize xc3
  | UInt32 n => serialize xce +$+ serialize n
  | Str32 s => serialize xdb +$+ serialize s
  | Map l => serialize xdf +$+ serialize (length l) +$+ serialize_list_MsgPack l
  end.

Definition MsgPack_deserialize :=
  tag <- deserialize;;
      match tag with
      | xc0 => ByteListReader.ret Nil
      | xc2 => ByteListReader.ret (Bool false)
      | xc3 => ByteListReader.ret (Bool true)
      | xce => UInt32 <$> deserialize
      | xdb => Str32 <$> deserialize
      | xdf => ByteListReader.error
      | _ => ByteListReader.error
      end.