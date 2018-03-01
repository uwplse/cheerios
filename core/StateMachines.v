Require Import Cheerios.Types.

Require Import List.

Import ListNotations.

Module Type STATE_MACHINE.
  Parameter run : forall {S A : Type},
    (state_machine S A) -> S -> list byte -> fold_state S (A * list byte).

  Parameter run_spec : forall {S A : Type}
                              (f : state_machine S A)
                              (s : S)
                              (l : list byte),
      run f s l =
      match l with
      | [] => More s
      | b :: l => match f b s with
                  | Done a => Done (a, l)
                  | More s => run f s l
                  | Error => Error
                  end
      end.

  Parameter pair : forall {S1 A S2 B},
      state_machine S1 A ->
      state_machine S2 B -> state_machine (S1 * S2 + A * S2) (A * B).

  Parameter run_pair_inr : forall S1 A S2 B
                                  (a : state_machine S1 A) (b : state_machine S2 B)
                                  x bytes s,
      run (pair a b) (inr (x, s)) bytes =
      match run b s bytes with
      | Done (y, l)  => Done ((x, y), l)
      | More s => More (inr (x, s))
      | Error => Error
      end.

  Parameter run_pair_inl : forall S1 A S2 B
                                  (a : state_machine S1 A) (b : state_machine S2 B)
                                  bytes s1 s2,
      run (pair a b) (inl (s1, s2)) bytes =
      match run a s1 bytes with
      | Done (x, l) => run (pair a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      | Error => Error
      end.

  Parameter sequence : forall {S1 A S2 B : Type},
      state_machine S1 A -> state_machine S2 B -> state_machine (S1 * (A -> S2) + S2) B.

  Parameter run_sequence_inr : forall S1 A S2 B
                                      (a : state_machine S1 A)
                                      (b : state_machine S2 B)
                                      bytes s,
      run (sequence a b) (inr s) bytes = match (run b s) bytes with
                                         | Done (x, l) => Done (x, l)
                                         | More s2 => More (inr s2)
                                         | Error => Error
                                         end.

  Parameter run_sequence_inl : forall S1 A S2 B
                                      (a : state_machine S1 A)
                                      (b : state_machine S2 B)
                                      bytes f s,
      run (sequence a b) (inl (s, f)) bytes =
      match run a s bytes with
      | Done (x, bytes) => run (sequence a b) (inr (f x)) bytes
      | More s1 => More (inl (s1, f))
      | Error => Error
      end.

  Parameter compose : forall {S1 A S2 B}, state_machine S1 A -> state_machine S2 B ->
                                          (A -> fold_state S2 B) -> state_machine (S1 + S2) B.

  Parameter map : forall {S A B}, (A -> B) -> state_machine S A -> state_machine S B.

  Parameter choice : forall {S1 A S2 B}, (state_machine S1 A) -> (state_machine S2 B) ->
                                         state_machine (S1 + S2) (A + B).
End STATE_MACHINE.

Module StateMachine : STATE_MACHINE.
  Fixpoint run {S A}
           (f : state_machine S A) (s : S) (l : list byte) : fold_state S (A * list byte) :=
    match l with
    | [] => More s
    | b :: l => match f b s with
                | Done a => Done (a, l)
                | More s => run f s l
                | Error => Error
                end
    end.

  Lemma run_spec : forall {S A : Type}
                          (f : state_machine S A)
                          (s : S)
                          (l : list byte),
      run f s l =
      match l with
      | [] => More s
      | b :: l => match f b s with
                  | Done a => Done (a, l)
                  | More s => run f s l
                  | Error => Error
                  end
      end.
  Proof.
    now destruct l.
  Qed.

  Lemma run_append :
    forall {S A : Type}  l1 l2 f (s : S),
      @run S A f s (l1 ++ l2) =
      match @run S A f s l1 with
      | More s' => @run S A f s' l2
      | Done (a, l1) => Done (a, l1 ++ l2)
      | Error => Error
      end.
  Proof.
    induction l1.
    - intros.
      reflexivity.
    - intros.
      simpl.
      destruct (f a s);
        try reflexivity.
      rewrite IHl1.
      reflexivity.
  Qed.


  (* pair *)
  Definition pair {S1 A S2 B}
             (a : state_machine S1 A)
             (b : state_machine S2 B) : state_machine (S1 * S2 + A * S2) (A * B) :=
    fun byte s =>
      match s with
      | inl (s1, s2) =>
        match a byte s1 with
        | Done x => More (inr (x, s2))
        | More s1 => More (inl (s1, s2))
        | Error => Error
        end
      | inr (x, s2) =>
        match b byte s2 with
        | Done b => Done (x, b)
        | More s2 => More (inr (x, s2))
        | Error => Error
        end
      end.

  Lemma run_pair_inr : forall S1 A S2 B
                              (a : state_machine S1 A) (b : state_machine S2 B)
                              x bytes s,
      run (pair a b) (inr (x, s)) bytes =
      match run b s bytes with
      | Done (y, l)  => Done ((x, y), l)
      | More s => More (inr (x, s))
      | Error => Error
      end.
  Proof.
    intros until bytes.
    induction bytes.
    - reflexivity.
    - intros s.
      unfold run.
      simpl.
      destruct (b _ _);
        auto.
  Qed.

  Lemma run_pair_inl : forall S1 A S2 B
                              (a : state_machine S1 A) (b : state_machine S2 B)
                              bytes s1 s2,
      run (pair a b) (inl (s1, s2)) bytes =
      match run a s1 bytes with
      | Done (x, l) => run (pair a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      | Error => Error
      end.
  Proof.
    intros until bytes.
    induction bytes.
    - reflexivity.
    - intros.
      simpl.
      destruct a; auto.
  Qed.


  (* sequence takes two state machines and produces a state machine that will:
     - run the first state machine
     - apply a user-supplied mapping to the first machine's output to get the
       initial state for the second machine, which will run from there *)
  Definition sequence {S1 A S2 B}
             (a : state_machine S1 A)
             (b : state_machine S2 B) : state_machine (S1 * (A -> S2) + S2) B :=
    fun byte s =>
      match s with
      | inl (s1, f) =>
        match a byte s1 with
        | Done x => More (inr (f x))
        | More s1 => More (inl (s1, f))
        | Error => Error
        end
      | inr s2 =>
        match b byte s2 with
        | Done b => Done b
        | More s2 => More (inr s2)
        | Error => Error
        end
      end.

  Lemma run_sequence_inl : forall S1 A S2 B
                                  (a : state_machine S1 A)
                                  (b : state_machine S2 B)
                                  bytes f s,
      run (sequence a b) (inl (s, f)) bytes =
      match run a s bytes with
      | Done (x, bytes) => run (sequence a b) (inr (f x)) bytes
      | More s1 => More (inl (s1, f))
      | Error => Error
      end.
  Proof.
    induction bytes.
    - reflexivity.
    - intros.
      simpl.
      destruct a;
        auto.
  Qed.

  Lemma run_sequence_inr : forall S1 A S2 B
                                  (a : state_machine S1 A)
                                  (b : state_machine S2 B)
                                  bytes s,
      run (sequence a b) (inr s) bytes = match (run b s) bytes with
                                         | Done (x, l) => Done (x, l)
                                         | More s2 => More (inr s2)
                                         | Error => Error
                                         end.
  Proof.
    induction bytes; simpl; intros.
    - reflexivity.
    - destruct b; auto.
  Qed.

  (* compose *)
  Definition compose {S1 A S2 B}
             (m1 : state_machine S1 A)
             (m2 : state_machine S2 B)
             (f : A -> fold_state S2 B) : state_machine (S1 + S2) B :=
    fun b s =>
      match s with
      | inl s1 => match m1 b s1 with
                  | Done a => match f a with
                              | Done b => Done b
                              | More s2 => More (inr s2)
                              | Error => Error
                              end
                  | More s1 => More (inl s1)
                  | Error => Error
                  end
      | inr s2 => match m2 b s2 with
                  | Done b => Done b
                  | More s2 => More (inr s2)
                  | Error => Error
                  end
      end.

    Lemma compose_run_inl :
    forall S1 A S2 B
           (a : state_machine S1 A) (b : state_machine S2 B) (f : A -> fold_state S2 B) l s1,
      run (compose a b f) (inl s1) l =
      match run a s1 l with
      | Done (x, l) =>
        match f x with
        | Done y => Done (y, l)
        | More s2 => run (compose a b f) (inr s2) l
        | Error => Error
        end
      | More s => More (inl s)
      | Error => Error
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
      destruct f; auto.
  Qed.

  Lemma compose_run_inr :
    forall S1 A S2 B
           (a : state_machine S1 A) (b : state_machine S2 B) (f : A -> fold_state S2 B) l s2,
      run (compose a b f) (inr s2) l =
      match run b s2 l with
      | Done (y, l) => Done (y, l)
      | More s => More (inr s)
      | Error => Error
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

  (* map *)
  Definition map {S A B} (f : A -> B) (m1: state_machine S A) : state_machine S B :=
    fun b s =>
      match m1 b s with
      | Done a => Done (f a)
      | More s => More s
      | Error => Error
      end.

  Lemma map_run :
    forall S A B (m : state_machine S A) (f : A -> B) l s,
      run (map f m) s l =
      match (run m s l) with
      | Done (x, l) => Done (f x, l)
      | More s => More s
      | Error => Error
      end.
  Proof.
    unfold map.
    induction l.
    - auto.
    - simpl. intros.
      destruct m; auto.
  Qed.

  (* choice *)
  Definition choice {S1 A S2 B} (m1 : state_machine S1 A) (m2 : state_machine S2 B) : state_machine (S1 + S2) (A + B) :=
    fun b s =>
      match s with
      | inl s1 => match m1 b s1 with
                  | Done x => Done (inl x)
                  | More s1 => More (inl s1)
                  | Error => Error
                  end

      | inr s2 => match m2 b s2 with
                  | Done y => Done (inr y)
                  | More s2 => More (inr s2)
                  | Error => Error
                  end
      end.

  Lemma run_choice_inl : forall S1 S2 A B (a : state_machine S1 A) (b : state_machine S2 B) l s,
      run (choice a b) (inl s) l =
      match run a s l with
      | Done (y, l) => Done (inl y, l)
      | More s => More (inl s)
      | Error => Error
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Lemma run_choice_inr : forall S1 S2 A B (a : state_machine S1 A) (b : state_machine S2 B) l s,
      run (choice a b) (inr s) l =
      match run b s l with
      | Done (y, l) => Done (inr y, l)
      | More s => More (inr s)
      | Error => Error
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.
End StateMachine.
