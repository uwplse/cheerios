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