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

  

  Parameter compose : forall {S1 A S2 B}, state_machine S1 A -> (state_machine S2 B) ->
                                          (A -> fold_state S2 B) -> state_machine (S1 + S2) B.


  Parameter map_sm : forall S A B, (A -> B) -> state_machine S A -> state_machine S B.

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

  Definition map_sm {S A B} (f : A -> B) (m1: state_machine S A) : state_machine S B :=
    fun b s =>
      match m1 b s with
      | Done a => Done (f a)
      | More s => More s
      | Error => Error
      end.
End StateMachine.
