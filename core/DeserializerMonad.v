Require Import Cheerios.Core.
Require Import Cheerios.Types.
Require Import List.
Import ListNotations.

Module DeserializerMonad (Reader : READER).
  Definition sequence {A B} (df : Reader.t (A -> B))
             (da : Reader.t A) : Reader.t B :=
    Reader.bind df
                (fun f =>
                   (Reader.bind da
                                (fun a => Reader.ret (f a)))).

  Lemma sequence_rewrite : forall {A B : Type}
                                  (df : Reader.t (A -> B))
                                  (da : Reader.t A),
      sequence df da =
      Reader.bind df
                  (fun f =>
                     (Reader.bind da
                                  (fun a => Reader.ret (f a)))).
  Proof.
    reflexivity.
  Qed.
  Hint Rewrite @sequence_rewrite : cheerios.

  Module DeserializerNotations.
    Notation "m >>= f" := (@Reader.bind _ _ m f) (at level 42, left associativity).

    Notation "x <- c1 ;; c2" := (c1 >>= (fun x => c2))
                                  (at level 100, c1 at next level, right associativity).
    Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                             (at level 100, right associativity).

    Notation "f <$> x" := (@Reader.map _ _ f x) (at level 42, left associativity).

    Notation "f <*> x" := (@sequence _ _ f x) (at level 42, left associativity).
  End DeserializerNotations.

  Check sequence.
  Import DeserializerNotations.

  Section lift.
    Import ByteListSerializer.
    Context {A B C D : Type}.
    Context {sA : Serializer A}.
    Context {sB : Serializer B}.
    Context {sC : Serializer C}.
    Context {sD : Serializer D}.
    Definition liftD1 {X} (f : D -> X) :=
      f <$> deserialize.

    Definition liftD2 {X} (f : C -> D -> X) : Reader.t X :=
      (f <$> deserialize) >>= liftD1.

    Definition liftD3 {X} (f : B -> C -> D -> X) : Reader.t X :=
      (f <$> deserialize) >>= liftD2.

    Definition liftD4 {X} (f : A -> B -> C -> D -> X) : Reader.t X :=
      (f <$> deserialize) >>= liftD3.
  End lift.
