Require Import List.
Import ListNotations.
Require Import Vectors.Vector.
Import VectorNotations.

Require Import Cheerios.Cheerios.

(* As a simple example, we can prove that a serialized pair of two As can be
  deserialized as a vector of As of length 2. *)
Section silly_example.
  Variables A : Type.
  Variable sA : Serializer A.

  Definition pair_to_vector (x : A * A) : Vector.t A 2 := [fst x; snd x].

  Lemma A_to_vector_triangle : triangle_spec pair_to_vector.
  Proof.
    destruct a; simpl; triangle_crush.
  Qed.
End silly_example.
