Require Import String.

Section Chord.

Variable id : Type.
Variable name : Type.

Record pointer := mkPointer { ptrId : id; ptrAddr : name }.

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

Definition addr := String.string.

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
