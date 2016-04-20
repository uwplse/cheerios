Require Import StructTact.StructTactics.
Require Import Cheerios.Monads.

Definition triple
           {S A : Type}
           (P : S -> Prop)
           (m : Maybe S A)
           (Q : A -> S -> Prop) : Prop :=
  forall s : S, P s ->
           match m s with
           | (None, _) => False
           | (Some a, s') => Q a s'
           end.

Lemma consequence : forall S A (P P' : S -> Prop) m (Q Q' : A -> S -> Prop),
    triple P m Q ->
    (forall s : S, P' s -> P s) ->
    (forall a s, Q a s -> Q' a s) ->
    triple P' m Q'.
Proof.
  unfold triple.
  intros.
  break_let.
  specialize (H s).
  find_rewrite.
  break_match; auto.
Qed.

Definition consequence_pre S A P P' m Q Hh Hp := consequence S A P P' m Q Q Hh Hp (fun a s q => q).
Definition consequence_post S A P m Q Q' Hh Hq := consequence S A P P m Q Q' Hh (fun s p => p) Hq.