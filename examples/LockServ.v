Inductive msg :=
| Lock : nat -> msg
| Unlock : msg
| Locked : nat -> msg.
