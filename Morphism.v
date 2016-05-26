Require Import List Fin.
Import ListNotations.

Require Import Core.
Require Import BasicSerializers.
Require Import Combinators.
Require Import Tactics.

(* A morphism between two serializable types A and B is a map A -> B that
   describes what happens if you serialize an A and then deserialize it *as a B*.
   This captures a binary-level compatibility between the serialization formats
   for A and B. *)

Local Notation triangle_spec f :=
  (forall a bin, deserialize (serialize a ++ bin) = Some (f a, bin)).

Class Morphism {A B : Type} (sA : Serializer A) (sB : Serializer B) : Type :=
{
  map : A -> B;
  triangle : triangle_spec map
}.

(* Like Candy Crush if the candy was triangular. *)
Ltac triangle_crush :=
intros;
deserializer_unfold;
repeat rewrite ?app_assoc_reverse, ?serialize_deserialize_id, ?triangle;
auto.

Eval cbv in serialize [1; 2; 3].

(* All the type constructors with serializers preserve morphisms. *)
Section morphism_combinators.
  Variables A B : Type.
  Variable sA : Serializer A.
  Variable sB : Serializer B.
  Variable m : Morphism sA sB.

  Lemma option_triangle : triangle_spec (option_map map).
  Proof.
    simpl.
    unfold option_deserialize, option_serialize.
    destruct a; triangle_crush.
  Qed.

  Global Instance option_Morphism : @t (option A) (option B) _ _ :=
    {| map := option_map map;
        triangle := option_triangle
    |}.


  Variables C : Type.
  Variable sC : Serializer C.


  Definition pair_l_map (f : A -> B) (x : A * C) : B * C :=
    let (a, c) := x in (f a, c).

  Lemma pair_l_triangle : triangle_spec (pair_l_map map).
  Proof.
    simpl.
    unfold pair_deserialize, pair_serialize.
    destruct a; triangle_crush.
  Qed.

  Global Instance pair_l_Morphism : @t (A * C) (B * C) _ _ :=
    {| map := pair_l_map map;
        triangle := pair_l_triangle
    |}.


  Definition pair_r_map (f : A -> B) (x : C * A) : C * B :=
    let (c, a) := x in (c, f a).

  Lemma pair_r_triangle : triangle_spec (pair_r_map map).
  Proof.
    simpl.
    unfold pair_deserialize, pair_serialize.
    destruct a; triangle_crush.
  Qed.

  Global Instance pair_r_Morphism : @t (C * A) (C * B) _ _ :=
    {| map := pair_r_map map;
        triangle := pair_r_triangle
    |}.


  Definition sum_l_map (f : A -> B) (x : A + C) : B + C :=
    match x with
    | inl a => inl (f a)
    | inr c => inr c
    end.

  Lemma sum_l_triangle : triangle_spec (sum_l_map map).
  Proof.
    simpl.
    unfold sum_serialize, sum_deserialize.
    destruct a; triangle_crush.
  Qed.

  Global Instance sum_l_Morphism : @t (A + C) (B + C) _ _ :=
    {| map := sum_l_map map;
        triangle := sum_l_triangle
    |}.


  Definition sum_r_map (f : A -> B) (x : C + A) : C + B :=
    match x with
    | inl c => inl c
    | inr a => inr (f a)
    end.

  Lemma sum_r_triangle : triangle_spec (sum_r_map map).
  Proof.
    simpl.
    unfold sum_serialize, sum_deserialize.
    destruct a; triangle_crush.
  Qed.

  Global Instance sum_r_Morphism : @t (C + A) (C + B) _ _ :=
    {| map := sum_r_map map;
        triangle := sum_r_triangle
    |}.


  Lemma list_triangle_rec:
    forall (a : list A) (bin : list bool),
      list_deserialize_rec B sB (length a) (list_serialize_rec A sA a ++ bin) =
      Some (List.map map a, bin).
  Proof.
    induction a; simpl; triangle_crush.
    now rewrite IHa.
  Qed.

  Lemma list_triangle : triangle_spec (@List.map A B map).
  Proof.
    simpl.
    unfold list_deserialize, list_serialize.
    serialize_deserialize_id_crush.
    apply list_triangle_rec.
  Qed.

  Global Instance list_morphism : @t (list A) (list B) _ _ :=
    {| map := List.map map;
        triangle := list_triangle
    |}.


  Lemma vector_triangle : forall n, triangle_spec (@Vector.map A B map n).
  Proof.
    induction a; simpl in *; triangle_crush.
    now rewrite IHa.
  Qed.

  Global Instance vector_morphism n : @t (Vector.t A n) (Vector.t B n) _ _ :=
    {| map := Vector.map map;
        triangle := vector_triangle n
    |}.
End morphism_combinators.