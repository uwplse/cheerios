Require Import String.
Require Import Bvector.

Require Import Cheerios.Core.
Require Import Cheerios.Combinators.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Tactics.
Require Import Cheerios.Types.

Import DeserializerNotations.

Section Chord.

Parameter N : nat.

Definition bit_len := 8 * N.

Definition id := Bvector.Bvector bit_len.
Definition addr := String.string.

(* pointer *)
Record pointer := mkPointer { ptrId : id; ptrAddr : addr }.


Definition pointer_serialize (ptr : pointer) : IOStreamWriter.t :=
  serialize (ptrId ptr) +$+ serialize (ptrAddr ptr).

Definition pointer_deserialize : ByteListReader.t pointer :=
  id <- deserialize;;
     addr <- deserialize;;
     ByteListReader.ret (mkPointer id addr).

Lemma pointer_serialize_deserialize_id : serialize_deserialize_id_spec pointer_serialize
                                                                       pointer_deserialize.
Proof.
  intros.
  unfold pointer_serialize, pointer_deserialize.
  destruct a.
  cheerios_crush.
Qed.

Instance pointer_Serializer : Serializer pointer.
Proof.
  exact {| serialize := pointer_serialize;
             deserialize := pointer_deserialize;
             serialize_deserialize_id := pointer_serialize_deserialize_id |}.
Qed.

(* payload *)
Inductive payload :=
| Busy : payload
| GetBestPredecessor : pointer -> payload
| GotBestPredecessor : pointer -> payload
| GetSuccList : payload
| GotSuccList : list pointer -> payload
| GetPredAndSuccs : payload
| GotPredAndSuccs : option pointer -> list pointer -> payload
| Notify : payload
| Ping : payload
| Pong : payload.

Definition payload_serialize (pl : payload) :=
  match pl with
  | Busy => serialize x00
  | GetBestPredecessor ptr => serialize x01 +$+ serialize ptr
  | GotBestPredecessor ptr => serialize x02 +$+ serialize ptr
  | GetSuccList => serialize x03
  | GotSuccList l => serialize x04 +$+ serialize l
  | GetPredAndSuccs => serialize x05
  | GotPredAndSuccs ptr l => serialize x06 +$+ serialize ptr +$+ serialize l
  | Notify => serialize x07
  | Ping => serialize x08
  | Pong => serialize x09
  end.

Definition payload_deserialize :=
  tag <- deserialize;;
      match tag with
      | x00 => ByteListReader.ret Busy
      | x01 => ptr <- deserialize;;
                   ByteListReader.ret (GetBestPredecessor ptr)
      | x02 => ptr <- deserialize;;
                   ByteListReader.ret (GotBestPredecessor ptr)
      | x03 => ByteListReader.ret GetSuccList
      | x04 => l <- deserialize;;
                 ByteListReader.ret (GotSuccList l)
      | x05 => ByteListReader.ret GetPredAndSuccs
      | x06 => ptr <- deserialize;;
                   l <- deserialize;;
                   ByteListReader.ret (GotPredAndSuccs ptr l)
      | x07 => ByteListReader.ret Notify
      | x08 => ByteListReader.ret Ping
      | x09 => ByteListReader.ret Pong
      | _ => ByteListReader.error
      end.

Lemma payload_serialize_deserialize_id : serialize_deserialize_id_spec payload_serialize
                                                                       payload_deserialize.
Proof.
  intros.
  unfold payload_serialize, payload_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance payload_Serializer : Serializer payload.
Proof.
  exact {| serialize := payload_serialize;
             deserialize := payload_deserialize;
             serialize_deserialize_id := payload_serialize_deserialize_id |}.
Qed.

(* timeout *)
Inductive timeout :=
| Tick : timeout
| RectifyTick : timeout
| KeepaliveTick : timeout
| Request : addr -> payload -> timeout.

Definition timeout_serialize (t : timeout) :=
  match t with
  | Tick => serialize x00
  | RectifyTick => serialize x01
  | KeepaliveTick => serialize x02
  | Request a pl => serialize x03 +$+ serialize a +$+ serialize pl
  end.

Definition timeout_deserialize :=
  tag <- deserialize;;
      match tag with
      | x00 => ByteListReader.ret Tick
      | x01 => ByteListReader.ret RectifyTick
      | x02 => ByteListReader.ret KeepaliveTick
      | x03 => a <- deserialize;;
                 pl <- deserialize;;
                 ByteListReader.ret (Request a pl)
      | _ => ByteListReader.error
      end.

Lemma timeout_serialize_deserialize_id : serialize_deserialize_id_spec timeout_serialize
                                                                       timeout_deserialize.
Proof.
  intros.
  unfold timeout_serialize, timeout_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance timeout_Serializer : Serializer timeout.
Proof.
  exact {| serialize := timeout_serialize;
             deserialize := timeout_deserialize;
             serialize_deserialize_id := timeout_serialize_deserialize_id |}.
Qed.

(* query *)
Inductive query :=
| Rectify : pointer -> query
| Stabilize : query
| Stabilize2 : pointer -> query
| Join : pointer -> query
| Join2 : pointer -> query.

Definition query_serialize (q : query) :=
  match q with
  | Rectify ptr => serialize x00 +$+ serialize ptr
  | Stabilize => serialize x01
  | Stabilize2 ptr => serialize x02 +$+ serialize ptr
  | Join ptr => serialize x03 +$+ serialize ptr
  | Join2 ptr => serialize x04 +$+ serialize ptr
  end.

Definition query_deserialize :=
  tag <- deserialize;;
      match tag with
      | x00 => ptr <- deserialize;;
                   ByteListReader.ret (Rectify ptr)
      | x01 => ByteListReader.ret Stabilize
      | x02 => ptr <- deserialize;;
                   ByteListReader.ret (Stabilize2 ptr)
      | x03 => ptr <- deserialize;;
                   ByteListReader.ret (Join ptr)
      | x04 => ptr <- deserialize;;
                   ByteListReader.ret (Join2 ptr)
      | _ => ByteListReader.error
      end.

Lemma query_serialize_deserialize_id : serialize_deserialize_id_spec query_serialize
                                                                       query_deserialize.
Proof.
  intros.
  unfold query_serialize, query_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance query_Serializer : Serializer query.
Proof.
  exact {| serialize := query_serialize;
             deserialize := query_deserialize;
             serialize_deserialize_id := query_serialize_deserialize_id |}.
Qed.
End Chord.
