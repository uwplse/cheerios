Require Import String.
Require Import Bvector.

Section Chord.

Parameter N : nat.

Definition bit_len := 8 * N.

Definition id := Bvector.Bvector bit_len.
Definition addr := String.string.

Record pointer := mkPointer { ptrId : id; ptrAddr : addr }.

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

Inductive timeout :=
| Tick : timeout
| RectifyTick : timeout
| KeepaliveTick : timeout
| Request : addr -> payload -> timeout.

Inductive query :=
| Rectify : pointer -> query
| Stabilize : query
| Stabilize2 : pointer -> query
| Join : pointer -> query
| Join2 : pointer -> query.

End Chord.
