Require Import List.
From Cheerios Require Import Monoid Core.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section deserializer.
  Variable bin: Type.
  Context {mbin : Monoid bin}.

  (* This is the monad used to write deserializers. It is a state monad with
      failure, where the state is the serialized bits. *)
  Definition deserializer A : Type := bin -> option (A * bin).

  Definition ret {A} (a : A) : deserializer A := fun s => Some (a, s).

  Definition bind {X Y} (m : deserializer X) (f : X -> deserializer Y) : deserializer Y :=
    fun s => match m s with None => None
                    | Some (a, s') => f a s'
          end.

  Definition get : deserializer bin := fun s => Some (s, s).

  Definition put (s : bin) : deserializer unit := fun _ => Some (tt, s).

  Definition fail {A} : deserializer A := fun _ => None.

  (* useful for "undoing" a deserialize step *)
  Definition push (l : bin) : deserializer unit := fun s => Some (tt, l +++ s).

  Definition fmap {X Y} (f : X -> Y) (x : deserializer X) : deserializer Y :=
    bind x (fun x => ret (f x)).

  Definition sequence {X Y} (df : deserializer (X -> Y)) (dx : deserializer X) : deserializer Y :=
    bind df (fun f => (bind dx (fun x => ret (f x)))).
End deserializer.

Module DeserializerNotations.
  Delimit Scope deserializer with deserializer.
  Open Scope deserializer.

  Notation "m >>= f" := (@bind _ _ _ m f) (at level 42, left associativity) : deserializer.

  Notation "x <- c1 ;; c2" := (c1 >>= (fun x => c2))
                                (at level 100, c1 at next level, right associativity) : deserializer.
  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                            (at level 100, right associativity) : deserializer.

  Notation "f <$> x" := (@fmap _ _ _ f x) (at level 42, left associativity) : deserializer.

  Notation "f <*> x" := (@sequence _ _ _ f x) (at level 42, left associativity) : deserializer.
End DeserializerNotations.

Import DeserializerNotations.

Section lift.
  Context {bin : Type}.
  Context {mbin : Monoid bin}.

  Context {A B C D : Type}.
  Context {sA : Serializer bin A}.
  Context {sB : Serializer bin B}.
  Context {sC : Serializer bin C}.
  Context {sD : Serializer bin D}.

  Definition liftD1 {X} (f : D -> X) : deserializer bin X :=
    f <$> deserialize.

  Definition liftD2 {X} (f : C -> D -> X) : deserializer bin X :=
    (f <$> deserialize) >>= liftD1.

  Definition liftD3 {X} (f : B -> C -> D -> X) : deserializer bin X :=
    (f <$> deserialize) >>= liftD2.

  Definition liftD4 {X} (f : A -> B -> C -> D -> X) : deserializer bin X :=
    (f <$> deserialize) >>= liftD3.
End lift.

Definition unwrap {bin} {A} (a : option A) : deserializer bin A :=
  match a with
  | Some a => ret a
  | None => fail
  end.

