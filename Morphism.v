Require Import List ZArith.
Import ListNotations.
From Cheerios Require Import Monoid Core Combinators Tactics.

(* A morphism between two serializable types A and B is a map A -> B that
   describes what happens if you serialize an A and then deserialize it *as a B*.
   This captures a binary-level compatibility between the serialization formats
   for A and B. *)

Notation triangle_spec f :=
  (forall a bin, deserialize (serialize a +++ bin) = Some (f a, bin)).

Class SerializerMorphism {A B bin : Type} {mbin : Monoid bin}
      (sA : Serializer bin A) (sB : Serializer bin B) : Type :=
{
  morphism : A -> B;
  triangle : triangle_spec morphism
}.

Lemma triangle_nil {A B bin : Type} {mbin : Monoid bin}
      {sA : Serializer bin A}
      {sB : Serializer bin B}
      {m : @SerializerMorphism A B bin mbin sA sB} :
  forall a : A, deserialize (serialize a) = Some (morphism a, mempty).
Proof.
  intros.
  pose proof triangle a mempty.
  now rewrite @mappend_mempty_r in *.
Qed.


Section morphism_combinators.
  Variable bin : Type.
  Variable mbin : Monoid bin.

  Context {sbool : Serializer bin bool}.
  Context {spos : Serializer bin positive}.

  Variables A B : Type.
  Variable sA : Serializer bin A.
  Variable sB : Serializer bin B.
  Variable m : SerializerMorphism sA sB.

  (* Unfortunately, typeclass resolution is not smart enough to use a version of this
     hint that is universally quantified over the morphism, so you have to put this line
     in every section where you want to define a combinator. *)

  Hint Rewrite (triangle(SerializerMorphism := m)) : cheerios.

  Lemma option_triangle :
    triangle_spec (option_map morphism).
  Proof.
    simpl.
    unfold option_deserialize, option_serialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance option_Morphism : @SerializerMorphism (option A) (option B) _ _ _ _ :=
    {|  morphism := option_map morphism;
        triangle := option_triangle
    |}.


  Variables C : Type.
  Variable sC : Serializer bin C.


  Definition pair_l_map (f : A -> B) (x : A * C) : B * C :=
    let (a, c) := x in (f a, c).

  Lemma pair_l_triangle : triangle_spec (pair_l_map morphism).
  Proof.
    simpl.
    unfold pair_deserialize, pair_serialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance pair_l_Morphism : @SerializerMorphism (A * C) (B * C) _ _ _ _ :=
    {|  morphism := pair_l_map morphism;
        triangle := pair_l_triangle
    |}.


  Definition pair_r_map (f : A -> B) (x : C * A) : C * B :=
    let (c, a) := x in (c, f a).

  Lemma pair_r_triangle : triangle_spec (pair_r_map morphism).
  Proof.
    simpl.
    unfold pair_deserialize, pair_serialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance pair_r_Morphism : @SerializerMorphism (C * A) (C * B) _ _ _ _ :=
    {| morphism := pair_r_map morphism;
        triangle := pair_r_triangle
    |}.


  Definition sum_l_map (f : A -> B) (x : A + C) : B + C :=
    match x with
    | inl a => inl (f a)
    | inr c => inr c
    end.

  Lemma sum_l_triangle : triangle_spec (sum_l_map morphism).
  Proof.
    simpl.
    unfold sum_serialize, sum_deserialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance sum_l_Morphism : @SerializerMorphism (A + C) (B + C) _ _ _ _ :=
    {| morphism := sum_l_map morphism;
        triangle := sum_l_triangle
    |}.


  Definition sum_r_map (f : A -> B) (x : C + A) : C + B :=
    match x with
    | inl c => inl c
    | inr a => inr (f a)
    end.

  Lemma sum_r_triangle : triangle_spec (sum_r_map morphism).
  Proof.
    simpl.
    unfold sum_serialize, sum_deserialize.
    destruct a; cheerios_crush.
  Qed.

  Global Instance sum_r_Morphism : @SerializerMorphism (C + A) (C + B) _ _ _ _ :=
    {| morphism := sum_r_map morphism;
        triangle := sum_r_triangle
    |}.


  Lemma list_triangle_rec:
    forall (a : list A) (data : bin),
      list_deserialize_rec _ B sB (length a) (list_serialize_rec bin A sA a +++ data) =
      Some (List.map morphism a, data).
  Proof.
    induction a; simpl; cheerios_crush.
    now rewrite IHa.
  Qed.

  Lemma list_triangle : triangle_spec (@List.map A B morphism).
  Proof.
    simpl.
    unfold list_deserialize, list_serialize.
    cheerios_crush.
    apply list_triangle_rec.
  Qed.

  Global Instance list_morphism : @SerializerMorphism (list A) (list B) _ _ _ _ :=
    {| morphism := List.map morphism;
        triangle := list_triangle
    |}.


  Lemma vector_triangle : forall n, triangle_spec (@Vector.map A B morphism n).
  Proof.
    induction a; simpl in *; cheerios_crush.
    now rewrite IHa.
  Qed.

  Global Instance vector_morphism n : @SerializerMorphism (Vector.t A n) (Vector.t B n) _ _ _ _ :=
    {| morphism := Vector.map morphism;
        triangle := vector_triangle n
    |}.

End morphism_combinators.
