Require Import List String.
Import ListNotations.

Class Monoid (A : Type) : Type :=
  { mempty : A;
    mappend : A -> A -> A;
    mappend_mempty_l : forall a, mappend mempty a = a;
    mappend_mempty_r : forall a, mappend a mempty = a;
    mappend_assoc : forall a b c, mappend (mappend a b) c = mappend a (mappend b c)
  }.

Notation "a +++ b" := (@mappend _ _ a b) (right associativity, at level 60) : monoid_scope.
Open Scope monoid_scope.

Instance ListMonoid {A} : Monoid (list A) :=
  {| mempty := [];
     mappend := @app A;
     mappend_mempty_l := fun a => eq_refl;
     mappend_mempty_r := @app_nil_r A;
     mappend_assoc := @app_ass A
  |}.
