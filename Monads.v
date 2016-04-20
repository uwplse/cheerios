Class Monad (M : Type -> Type) : Type :=
  Pack
    {
      ret : forall {A}, A -> M A;
      bind : forall {A B}, M A -> (A -> M B) -> M B
    }.

Notation "x <- c1 ;; c2" :=
  (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).
Notation "e1 ;; e2" :=
  (_ <- e1 ;; e2)
    (at level 100, right associativity).

Definition Maybe (S : Type) (A : Type) :=
  S -> (option A * S).

Definition maybeRet {S A : Type} (x : A) : Maybe S A :=
  fun s => (Some x, s).

Definition maybeBind
           {S A B : Type}
           (m : Maybe S A)
           (f : A -> Maybe S B) : Maybe S B :=
  fun s =>
    match m s with
    | (None, s') => (None, s')
    | (Some a, s') => f a s'
    end.

Definition get {S : Type} : Maybe S S :=
  fun s => (Some s, s).

Definition put {S : Type} (s : S) : Maybe S unit :=
  fun _ => (Some tt, s).

Definition modify {S : Type} (f : S -> S) : Maybe S unit :=
  maybeBind get (fun s => put (f s)).

Definition fail {S A : Type} : Maybe S A :=
  fun (s:S) => (@None A, s).

Instance maybe_monad (S : Type) : Monad (Maybe S) :=
  Pack (Maybe S) (@maybeRet S) (@maybeBind S).