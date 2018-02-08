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

Definition LockservTag_sm : unit -> (byte -> fold_state unit LockservTag) + LockservTag :=
  fun _ => inl (fun b => match b with
                         | x00 => Done LockTag
                         | x01 => Done UnlockTag
                         | x02 => Done LockedTag
                         | _ => Error
                         end).


Parameter nat_sm_t : Type.
Parameter nat_sm_step : byte -> nat_sm_t -> fold_state nat_sm_t nat.
Parameter nat_sm_init : nat_sm_t.

Definition nat_sm_step' : nat_sm_t -> (byte -> fold_state nat_sm_t nat) + nat :=
  fun ns => inl (fun b => nat_sm_step b ns).

Inductive lockserv_sm_t :=
| Tag
| Body : LockservTag * nat_sm_t -> lockserv_sm_t.

Definition LocskervMsg_deserialize_manual
           (b : byte)
           (s: lockserv_sm_t) : fold_state lockserv_sm_t LockservMsg :=
  match s with
  | Tag => match b with
           | x00 => More (Body (LockTag, nat_sm_init))
           | x01 => Done Unlock
           | x02 => More (Body (LockedTag, nat_sm_init))
           | _ => Error
           end
  | Body (t, ns) => match nat_sm_step b ns with
                    | Done n => match t with
                                | LockTag => Done (Lock n)
                                | UnlockTag => Error
                                | LockedTag => Done (Locked n)
                                end
                    | More ns => More (Body (t, ns))
                    | Error => Error
                    end
  end.

Definition Lockserv_tag_sm : unit -> (byte -> fold_state unit LockservTag) + LockservTag :=
  fun _ => inl (fun b => match b with
                         | x00 => Done LockTag
                         | x01 => Done UnlockTag
                         | x02 => Done LockedTag
                         | _ => Error
                         end).

Definition Lockserv_body_sm (t : LockservTag) (s : nat_sm_t + (nat * unit))
  : (byte -> fold_state (nat_sm_t + nat * unit) LockservMsg) + LockservMsg :=
    match t with
    | LockTag =>  inr Unlock
    | UnlockTag => inr Unlock
    | LockedTag => inr Unlock
    end.

Definition lockserv_deserialize :=
  ByteListReader.bind_sm Lockserv_tag_sm
                         Lockserv_body_sm.