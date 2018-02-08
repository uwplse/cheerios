Require Import String.

Definition key := string.
Definition value := string.

Inductive input : Set :=
| Put : key -> value -> input
| Get : key -> input
| Del : key -> input
| CAS : key -> option value -> value -> input
| CAD : key -> value -> input.

Inductive output : Set :=
| Response : key -> option value -> option value -> output.
