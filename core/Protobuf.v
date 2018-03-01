Require Import Cheerios.Core.
Require Import Cheerios.StateMachines.
Require Import Cheerios.Types.

Require Import Strings.String.


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
| Unlock : LockservMsg
| Lock : nat -> LockservMsg
| Locked : nat -> LockservMsg.

Parameter nat_sm_t : Type.
Parameter nat_sm : state_machine nat_sm_t nat.
Parameter nat_sm_init : nat_sm_t.

Inductive Lockserv_sm_t :=
| UnlockTag
| LockTag
| LockedTag.

Definition LockservMsg_deserialize_tag : state_machine unit Lockserv_sm_t :=
  fun (byte : byte) _ =>
    match byte with
    | x00 => Done UnlockTag
    | x01 => Done LockTag
    | x02 => Done LockedTag
    | _ => Error
    end.

Definition a (x : nat + nat + nat) : nat :=
  match x with
  | inl (inl x) => x
  | inl (inr x) => x
  | inr x => x
  end.

Definition intermediate_sm :=
  StateMachine.map
    (fun x => match x with
              | inl n => Lock n
              | inr n => Locked n
              end)
    (StateMachine.choice nat_sm nat_sm).

Definition LockservMsg_msg_sm :=
  StateMachine.compose LockservMsg_deserialize_tag
                       intermediate_sm
                       (fun tag => match tag with
                                   | UnlockTag => Done Unlock
                                   | LockTag => More (inl nat_sm_init)
                                   | LockedTag => More (inr nat_sm_init)
                                   end).