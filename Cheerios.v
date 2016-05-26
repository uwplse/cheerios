Require Import List ZArith.
Import ListNotations.

From StructTact Require Import StructTactics Fin.

Require Vector Fin.

Module Deserializer.
  (* This is the monad used to write deserializers. It is a state monad with
     failure, where the state is the serialized bits. *)
  Definition t (A : Type) : Type := list bool -> option (A * list bool).

  Definition ret {A} (a : A) : t A := fun s => Some (a, s).

  Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
    fun s => match m s with None => None
                    | Some (a, s') => f a s'
          end.

  Definition get : t (list bool) := fun s => Some (s, s).

  Definition put (s : list bool) : t unit := fun _ => Some (tt, s).

  Definition fail {A} : t A := fun _ => None.


  Definition fmap {A B} (f : A -> B) (x : t A) : t B :=
    bind x (fun a => ret (f a)).

  Definition sequence {A B} (df : t (A -> B)) (da : t A) : t B :=
    bind df (fun f => (bind da (fun a => ret (f a)))).

  Module DeserializerNotations.
    Notation "m >>= f" := (@bind _ _ m f) (at level 42, left associativity).

    Notation "x <- c1 ;; c2" := (c1 >>= (fun x => c2))
                                  (at level 100, c1 at next level, right associativity).
    Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                             (at level 100, right associativity).

    Notation "f <$> x" := (@fmap _ _ f x) (at level 42, left associativity).

    Notation "f <*> x" := (@sequence _ _ f x) (at level 42, left associativity).
  End DeserializerNotations.

  Ltac deserializer_unfold :=
    unfold (* list in reverse order so that dependencies get unfolded *)
      sequence,
      fmap,
      fail,
      put,
      get,
      bind,
      ret
    in *.
End Deserializer.

Import Deserializer.
Import DeserializerNotations.

Local Notation serialize_deserialize_id_spec s d :=
  (forall a (bin : list bool), d (s a ++ bin) = Some (a, bin)).

(* This is the class of serializable types, which is the main entrypoint to
   Cheerios. Instances are required to show that `deserialize` can correctly
   recognize a piece of `serialize`d data at the prefix of an arbitrary
   bitstream. *)
Class Serializer (A : Type) : Type :=
  {
    serialize : A -> list bool;
    deserialize : Deserializer.t A;
    serialize_deserialize_id : serialize_deserialize_id_spec serialize deserialize
  }.

(* In particular, if there is nothing else in the bitsream, then deserialize and
   serialize are inverses. *)
Lemma serialize_deserialize_id_nil :
  forall A (sA : Serializer A) a, deserialize (serialize a) = Some (a, []).
Proof.
  intros.
  pose proof serialize_deserialize_id a [].
  now rewrite app_nil_r in *.
Qed.

Ltac serialize_deserialize_id_crush :=
  intros; deserializer_unfold;
  repeat rewrite ?app_assoc_reverse, ?serialize_deserialize_id;
  auto.


(* The two basic serializers are those for bool and positive. Both directly
   manipulate the state monad or its concrete implementation. All other
   serializers use generic monad combinators to perform serialization. *)

Definition bool_serialize (b : bool) : list bool := [b].

Definition bool_deserialize : Deserializer.t bool :=
  l <- get ;;
  match l with
  | [] => fail
  | b :: l' => put l' ;; ret b
  end.

Lemma bool_serialize_deserialize_id :
  serialize_deserialize_id_spec bool_serialize bool_deserialize.
Proof.
  destruct a; auto.
Qed.

Instance bool_Serializer : Serializer bool :=
  {| serialize := bool_serialize;
     deserialize := bool_deserialize;
     serialize_deserialize_id := bool_serialize_deserialize_id
  |}.


(* This is about 2x less space-efficient than necessary, since it outputs two
   bits for every "bit" in the input, but it's very easy to verify. *)
Fixpoint positive_serialize (p : positive) : list bool :=
  match p with
  | xI p' => serialize true ++ serialize true ++ positive_serialize p'
  | xO p' => serialize true ++ serialize false ++ positive_serialize p'
  | xH => serialize false
  end.

(* This has to be implemented directly on the implementation of Deserializer.t
   because it performs recursion on the underlying list of bits. *)
Fixpoint positive_deserialize (l : list bool) : option (positive * list bool) :=
  match l with
  | [] => None
  | continue :: l' =>
    if continue
    then match l' with
         | [] => None
         | bit :: l' => match positive_deserialize l' with None => None
                       | Some (p, l') => Some ((if bit then xI else xO) p, l')
                       end
         end
    else Some (xH, l')

  end.

Lemma positive_serialize_deserialize_id :
  forall p bin, positive_deserialize (positive_serialize p ++ bin) = Some (p, bin).
Proof.
  induction p; simpl; intros; auto; rewrite IHp; auto.
Qed.

Instance positive_Serializer : Serializer positive :=
  {| serialize := positive_serialize;
     deserialize := positive_deserialize;
     serialize_deserialize_id := positive_serialize_deserialize_id
  |}.


(* This is the first example of a "typical" serializer: it combines more
   primitive serializers (in this case, just for bool and positive) together in
   order to serialize a Z. *)
Definition Z_serialize (z : Z) : list bool :=
  match z with
  | Z0 => serialize false
  | Zpos p => serialize true ++ serialize true ++ serialize p
  | Zneg p => serialize true ++ serialize false ++ serialize p
  end.

Definition Z_deserialize : Deserializer.t Z :=
  tag <- deserialize ;;
  match tag with
  | true => sign <- deserialize ;;
           (match sign with true => Zpos | false => Zneg end) <$> deserialize
  | false => ret Z0
  end.

(* This proof is typical for serializing an algebraic datatype. Unfold the
   serializer and deserializer, then do a case analysis and call
   serialize_deserialize_id_crush. *)
Lemma Z_serialize_deserialize_id :
  serialize_deserialize_id_spec Z_serialize Z_deserialize.
Proof.
  unfold Z_serialize, Z_deserialize.
  destruct a; serialize_deserialize_id_crush.
Qed.

Instance Z_Serializer : Serializer Z :=
  {| serialize := Z_serialize;
     deserialize := Z_deserialize;
     serialize_deserialize_id := Z_serialize_deserialize_id
  |}.


Definition N_serialize (n : N) : list bool :=
  match n with
  | N0 => serialize false
  | Npos p => serialize true ++ serialize p
  end.

Definition N_deserialize : Deserializer.t N :=
  tag <- deserialize ;;
  match tag with
  | false => ret N0
  | true => Npos <$> deserialize
  end.

Lemma N_serialize_deserialize_id :
  serialize_deserialize_id_spec N_serialize N_deserialize.
Proof.
  unfold N_serialize, N_deserialize.
  destruct a; serialize_deserialize_id_crush.
Qed.

Instance N_Serializer : Serializer N :=
  {| serialize := N_serialize;
     deserialize := N_deserialize;
     serialize_deserialize_id := N_serialize_deserialize_id
  |}.


(* The other main way to define a serializer is to use an isomorphism to another
   type that is already serializable. *)
Definition nat_serialize (n : nat) : list bool := serialize (N.of_nat n).

Definition nat_deserialize : Deserializer.t nat := N.to_nat <$> deserialize.

(* This proof is typical for serializers defined by converting to and from a
   type that is already serializable. Unfold the serializer and deserializer,
   call serialize_deserialize_id_crush, and then use the proof that the
   conversion functions are inverses. *)
Lemma nat_serialize_deserialize_id :
  serialize_deserialize_id_spec nat_serialize nat_deserialize.
Proof.
  unfold nat_serialize, nat_deserialize.
  serialize_deserialize_id_crush.
  now rewrite Nnat.Nat2N.id.
Qed.

Instance nat_Serializer : Serializer nat :=
  {| serialize := nat_serialize;
     deserialize := nat_deserialize;
     serialize_deserialize_id := nat_serialize_deserialize_id
  |}.


(* Serializer for the standard library's Fin.t based on converting to nat. *)
Definition Fin_serialize {n} (x : Fin.t n) : list bool :=
  serialize (proj1_sig (Fin.to_nat x)).

Definition Fin_deserialize {n} : Deserializer.t (Fin.t n) :=
  m <- deserialize ;;
    match Fin.of_nat m n with
    | inleft x => ret x
    | inright _ => fail
    end.

Lemma Fin_of_nat_to_nat:
  forall (n : nat) (a : Fin.t n), Fin.of_nat (proj1_sig (Fin.to_nat a)) n = inleft a.
Proof.
  induction a.
  - auto.
  - simpl. break_let. simpl in *.
    now rewrite IHa.
Qed.

Lemma Fin_serialize_deserialize_id n : serialize_deserialize_id_spec Fin_serialize (@Fin_deserialize n).
Proof.
  unfold Fin_serialize, Fin_deserialize.
  serialize_deserialize_id_crush.
  now rewrite Fin_of_nat_to_nat.
Qed.

Instance Fin_Serializer n : Serializer (Fin.t n) :=
  {| serialize := Fin_serialize;
     deserialize := Fin_deserialize;
     serialize_deserialize_id := Fin_serialize_deserialize_id n
  |}.


(* Serializer for StructTact's fin based on converting to nat. *)
Definition fin_serialize {n} (x : fin n) : list bool :=
  serialize (fin_to_nat x).

Definition fin_deserialize {n} : Deserializer.t (fin n) :=
  m <- deserialize ;;
    match fin_of_nat m n with
    | inleft x => ret x
    | inright _ => fail
    end.

Lemma fin_serialize_deserialize_id n : serialize_deserialize_id_spec fin_serialize (@fin_deserialize n).
Proof.
  unfold fin_serialize, fin_deserialize.
  serialize_deserialize_id_crush.
  now rewrite fin_of_nat_fin_to_nat.
Qed.

Instance fin_Serializer n : Serializer (fin n) :=
  {| serialize := fin_serialize;
     deserialize := fin_deserialize;
     serialize_deserialize_id := fin_serialize_deserialize_id n
  |}.


(* These functions are either missing obvious implicits, or have
   implicit arguments that are not marked "maximally inserted", which
   means they cannot easily be used with map or fmap. *)
Arguments Some {_} _.
Arguments cons {_} _ _.
Arguments option_map {_ _} _ _.
Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.


(* This section gives instances for various type constructors, including pairs
   and lists. *)
Section combinators.
  Variables A B : Type.
  Variable sA : Serializer A.
  Variable sB : Serializer B.

  Definition option_serialize (x : option A) : list bool :=
    match x with
    | Some a => serialize true ++ serialize a
    | None => serialize false
    end.

  Definition option_deserialize : Deserializer.t (option A) :=
    b <- deserialize ;;
    match b with
    | true => Some <$> deserialize
    | false => ret None
    end.

  Lemma option_serialize_deserialize_id :
    serialize_deserialize_id_spec option_serialize option_deserialize.
  Proof.
    unfold option_serialize, option_deserialize.
    destruct a; serialize_deserialize_id_crush.
  Qed.

  Global Instance option_Serializer : Serializer (option A) :=
    {| serialize := option_serialize;
       deserialize := option_deserialize;
       serialize_deserialize_id := option_serialize_deserialize_id
    |}.


  Definition pair_serialize (x : A * B) : list bool :=
    let (a, b) := x in serialize a ++ serialize b.

  Definition pair_deserialize : Deserializer.t (A * B) :=
    pair <$> deserialize <*> deserialize.

  Lemma pair_serialize_deserialize_id :
    serialize_deserialize_id_spec pair_serialize pair_deserialize.
  Proof.
    unfold pair_serialize, pair_deserialize.
    destruct a; serialize_deserialize_id_crush.
  Qed.

  Global Instance pair_Serializer : Serializer (A * B) :=
    {| serialize := pair_serialize;
       deserialize := pair_deserialize;
       serialize_deserialize_id := pair_serialize_deserialize_id
    |}.


  Definition sum_serialize (x : A + B) : list bool :=
    match x with
    | inl a => serialize true ++ serialize a
    | inr b => serialize false ++ serialize b
    end.

  Definition sum_deserialize : Deserializer.t (A + B) :=
    b <- deserialize ;;
    match b with
    | true => inl <$> deserialize
    | false => inr <$> deserialize
    end.

  Lemma sum_serialize_deserialize_id :
    serialize_deserialize_id_spec sum_serialize sum_deserialize.
  Proof.
    unfold sum_serialize, sum_deserialize.
    destruct a; serialize_deserialize_id_crush.
  Qed.

  Global Instance sum_Serializer : Serializer (A + B) :=
    {| serialize := sum_serialize;
       deserialize := sum_deserialize;
       serialize_deserialize_id := sum_serialize_deserialize_id
    |}.


  Fixpoint list_serialize_rec (l : list A) : list bool :=
    match l with
    | [] => []
    | a :: l' => serialize a ++ list_serialize_rec l'
    end.

  Definition list_serialize (l : list A) : list bool :=
    serialize (length l) ++ list_serialize_rec l.

  Fixpoint list_deserialize_rec (n : nat) : Deserializer.t (list A) :=
    match n with
    | 0 => ret []
    | S n' => cons <$> deserialize <*> list_deserialize_rec n'
    end.

  Definition list_deserialize : Deserializer.t (list A) :=
    deserialize >>= list_deserialize_rec.

  Lemma list_serialize_deserialize_id_rec :
    forall l bin, list_deserialize_rec (length l) (list_serialize_rec l ++ bin) = Some (l, bin).
  Proof.
    induction l; simpl; serialize_deserialize_id_crush.
    now rewrite IHl.
  Qed.

  Lemma list_serialize_deserialize_id :
    serialize_deserialize_id_spec list_serialize list_deserialize.
  Proof.
    unfold list_serialize, list_deserialize.
    serialize_deserialize_id_crush.
    apply list_serialize_deserialize_id_rec.
  Qed.

  Global Instance list_Serializer : Serializer (list A) :=
    {| serialize := list_serialize;
       deserialize := list_deserialize;
       serialize_deserialize_id := list_serialize_deserialize_id
    |}.


  Fixpoint vector_serialize {n} (v : Vector.t A n) : list bool :=
    match v with
    | Vector.nil => []
    | Vector.cons a v' => serialize a ++ vector_serialize v'
    end.

  Fixpoint vector_deserialize {n} : Deserializer.t (Vector.t A n) :=
    match n as n0 return Deserializer.t (Vector.t A n0) with
    | 0 => ret Vector.nil
    | S n' => a <- deserialize ;; v <- vector_deserialize ;; ret (Vector.cons a v)
    end.

  Lemma vector_serialize_deserialize_id :
    forall n, serialize_deserialize_id_spec vector_serialize (@vector_deserialize n).
  Proof.
    induction n; intros.
    - destruct a using Vector.case0. auto.
    - destruct a using Vector.caseS'.
      simpl.
      serialize_deserialize_id_crush.
      now rewrite IHn.
  Qed.

  Global Instance vector_Serializer n : Serializer (Vector.t A n) :=
    {| serialize := vector_serialize;
       deserialize := vector_deserialize;
       serialize_deserialize_id := vector_serialize_deserialize_id n
    |}.
End combinators.

(* A morphism between two serializable types A and B is a map A -> B that
   describes what happens if you serialize an A and then deserialize it *as a B*.
   This captures a binary-level compatibility between the serialization formats
   for A and B. *)
Module Morphism.
  Local Notation triangle_spec f :=
    (forall a bin, deserialize (serialize a ++ bin) = Some (f a, bin)).

  Class t {A B : Type} (sA : Serializer A) (sB : Serializer B) : Type :=
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


  (* As a simple example, we can prove that a serialized pair of two As can be
     deserialized as a vector of As of length 2. *)
  Module silly_example.
    Import Vector.VectorNotations.
    Section silly_example.
      Variables A : Type.
      Variable sA : Serializer A.

      Definition pair_to_vector (x : A * A) : Vector.t A 2 := [fst x; snd x].

      Lemma A_to_vector_triangle : triangle_spec pair_to_vector.
      Proof.
        destruct a; simpl; triangle_crush.
      Qed.
    End silly_example.
  End silly_example.

  (* All the type constructors with serializers preserve morphisms. *)
  Section morphism_combinators.
    Variables A B : Type.
    Variable sA : Serializer A.
    Variable sB : Serializer B.
    Variable m : t sA sB.


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
End Morphism.
