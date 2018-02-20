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

Inductive LockservTag :=
| LockTag
| UnlockTag
| LockedTag.

Definition LockservMsg_deserialize_tag : state_machine unit LockservTag :=
  fun (byte : byte) _ =>
    match byte with
    | x00 => Done LockTag
    | x01 => Done UnlockTag
    | x02 => Done LockedTag
    | _ => Error
    end.

Definition LockservMsg_deserialize_tag_value :=
  ByteListReader.bind_sm LockservMsg_deserialize_tag
                         (fun tag => match tag with
                                     | LockTag => fun b _ => Done (Lock (byte_to_nat b))
                                     | UnlockTag => fun _ _ => Done Unlock
                                     | LockedTag => fun b _ => Done (Locked (byte_to_nat b))
                                     end)
                         (fun _ => tt).
