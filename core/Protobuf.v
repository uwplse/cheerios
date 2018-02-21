Require Import Cheerios.BasicSerializers.
Require Import Cheerios.ByteDecidable.
Require Import Cheerios.Core.
Require Import Strings.String.
Require Import Cheerios.Types.

Definition int32 := nat.
Definition ident := string.


Inductive field_type :=
| Int32Type
| BoolType
| MessageType.

Inductive field :=
| A : bool (* repeated? *) ->
      field_type -> ident -> int32 -> field.

Inductive msg :=
| Msg : nat -> msg_body -> msg
with msg_body :=
     | Nil : msg_body
     | Enum : msg_body
     | Cons : msg -> msg_body.

Inductive LockservMsg :=
| Lock : nat -> LockservMsg
| Unlock : LockservMsg
| Locked : nat -> LockservMsg.

Parameter nat_sm_t : Type.
Parameter nat_sm : state_machine nat_sm_t nat.
Parameter nat_sm_init : nat_sm_t.

Inductive Lockserv_sm_t :=
| LockTag : nat_sm_t -> Lockserv_sm_t
| UnlockTag : Lockserv_sm_t
| LockedTag : nat_sm_t -> Lockserv_sm_t.

Definition LockservMsg_deserialize_tag : state_machine unit Lockserv_sm_t :=
  fun (byte : byte) _ =>
    match byte with
    | x00 => Done (LockTag nat_sm_init)
    | x01 => Done UnlockTag
    | x02 => Done (LockedTag nat_sm_init)
    | _ => Error
    end.

Definition LockservMsg_deserialize_tag_value :=
  ByteListReader.compose LockservMsg_deserialize_tag
                         (fun b s => match s with
                                     | LockTag s => match nat_sm b s with
                                                    | Done n => Done (Lock n)
                                                    | More s => More (LockTag s)
                                                    | Error => Error
                                                    end
                                     | UnlockTag => Error
                                     | LockedTag s => match nat_sm b s with
                                                       | Done n => Done (Locked n)
                                                       | More s => More (LockedTag s)
                                                       | Error => Error
                                                       end
                                     end)
                         (fun t => match t with
                                   | LockTag s => More (LockTag s)
                                   | UnlockTag => Done Unlock
                                   | LockedTag s => More (LockedTag s)
                                   end).
