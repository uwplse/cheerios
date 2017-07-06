Require Import List.
Import ListNotations.
Require Import Cheerios.BasicSerializers.
Require Import Cheerios.Combinators.
Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Tactics.
Require Import Cheerios.Types.

(* A morphism between two serializable types A and B is a map A -> B that
   describes what happens if you serialize an A and then deserialize it *as a B*.
   This captures a binary-level compatibility between the serialization formats
   for A and B. *)

Notation triangle_spec f :=
  (forall a bin,
      Deserializer.unwrap deserialize (Serializer.unwrap (serialize a) ++ bin) = Some (f a, bin)).

Class SerializerMorphism {A B : Type} (sA : Serializer A) (sB : Serializer B) : Type :=
{
  morphism : A -> B;
  triangle : triangle_spec morphism
}.

Lemma triangle_nil {A B sA sB} {m : @SerializerMorphism A B sA sB}  :
  forall a,
    Deserializer.unwrap deserialize (Serializer.unwrap (serialize a)) =
    Some (morphism a, []).
Proof.
  intros.
  pose proof triangle a [].
  now rewrite app_nil_r in *.
Qed.

(* Like Candy Crush if the candy was triangular. *)
Ltac triangle_crush :=
  intros;
  cheerios_crush;
  repeat rewrite ?app_assoc_reverse, ?serialize_deserialize_id, ?triangle;
  cheerios_crush.

(*

Section morphism_combinators.

  Variables A B : Type.
  Variable sA : Serializer A.
  Variable sB : Serializer B.
  Variable m : SerializerMorphism sA sB.

  Lemma option_triangle : triangle_spec (option_map morphism).
  Proof.
    simpl.
    destruct a.
    - intros. destruct m.
      
  Qed.

  Global Instance option_Morphism : @SerializerMorphism (option A) (option B) _ _ :=
    {|  morphism := option_map morphism;
        triangle := option_triangle
    |}.


  Variables C : Type.
  Variable sC : Serializer C.


  Definition pair_l_map (f : A -> B) (x : A * C) : B * C :=
    let (a, c) := x in (f a, c).

  Lemma pair_l_triangle : triangle_spec (pair_l_map morphism).
  Proof.
    simpl.
    unfold pair_deserialize, pair_serialize.
    destruct a;
      triangle_crush.
  Qed.

  Global Instance pair_l_Morphism : @SerializerMorphism (A * C) (B * C) _ _ :=
    {|  morphism := pair_l_map morphism;
        triangle := pair_l_triangle
    |}.


  Definition pair_r_map (f : A -> B) (x : C * A) : C * B :=
    let (c, a) := x in (c, f a).

  Lemma pair_r_triangle : triangle_spec (pair_r_map morphism).
  Proof.
    simpl.
    unfold pair_deserialize, pair_serialize.
    destruct a; triangle_crush.
  Qed.

  Global Instance pair_r_Morphism : @SerializerMorphism (C * A) (C * B) _ _ :=
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
    destruct a; triangle_crush.
  Qed.

  Global Instance sum_l_Morphism : @SerializerMorphism (A + C) (B + C) _ _ :=
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
    destruct a; triangle_crush.
  Qed.

  Global Instance sum_r_Morphism : @SerializerMorphism (C + A) (C + B) _ _ :=
    {| morphism := sum_r_map morphism;
        triangle := sum_r_triangle
    |}.


  Lemma list_triangle_rec:
    forall (a : list A) (bytes : list byte),
      Deserializer.unwrap (list_deserialize_rec B sB (length a))
                          (Serializer.unwrap (list_serialize_rec A sA a) ++ bytes) =
      Some (List.map morphism a, bytes).
  Proof.
    induction a;
      intros;
      unfold list_serialize_rec, list_deserialize_rec;
      simpl;
      triangle_crush;
      rewrite IHa;
      cheerios_crush.
  Qed.

  Lemma list_triangle : triangle_spec (@List.map A B morphism).
  Proof.
    simpl.
    unfold list_deserialize, list_serialize.
    cheerios_crush.
    apply list_triangle_rec.
  Qed.

  Global Instance list_morphism : @SerializerMorphism (list A) (list B) _ _ :=
    {| morphism := List.map morphism;
        triangle := list_triangle
    |}.


  Lemma vector_triangle : forall n, triangle_spec (@Vector.map A B morphism n).
  Proof.
    induction a; simpl in *; triangle_crush.
    rewrite IHa.
    cheerios_crush.
  Qed.

  Global Instance vector_morphism n : @SerializerMorphism (Vector.t A n) (Vector.t B n) _ _ :=
    {| morphism := Vector.map morphism;
        triangle := vector_triangle n
    |}.

End morphism_combinators.

*)