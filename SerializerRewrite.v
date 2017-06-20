
Require Import List ZArith.
Import ListNotations.
Set Implicit Arguments.

(* type definitions *)

Inductive writer : Type :=
| Writer : list bool -> writer.

Inductive deserializer A : Type :=
| Deserializer : (list bool -> option (A * list bool)) -> deserializer A.

(* writer primitives *)

Definition empty : writer := Writer [].

Definition append (w1 w2: writer) : writer := 
  match (w1, w2) with
  | (Writer l1, Writer l2) =>  Writer (l1 ++ l2)
  end.

Definition mapWriter {A B} (f : A -> B) (wB : B -> writer) : A -> writer :=
  fun a => wB (f a).  

Definition putBit (b : bool) : writer := Writer [b].

(* deserializer primitives *)

Definition getBit : deserializer bool :=
  Deserializer
    (fun l =>
       match l with
       | [] => None
       | b :: l => Some (b, l)
       end).

Definition unwrap_s (w : writer) :=
  match w with
  | Writer l => l
  end.

Lemma putBit_unwrap : forall b, unwrap_s (putBit b) = [b].
Proof.
  reflexivity.
Qed.
Hint Rewrite putBit_unwrap.

Lemma append_unwrap : forall s1 s2,
    unwrap_s (append s1 s2) = unwrap_s s1 ++ unwrap_s s2.
Proof.
  destruct s1.
  destruct s2.
  reflexivity.
Qed.
Hint Rewrite append_unwrap : cheerios.

Lemma mapWriter_unwrap : forall {A B : Type} (f : A -> B) s (a : A),
    unwrap_s ((mapWriter f s) a) = (unwrap_s (s (f a))).
Proof.
  intros.
  unfold mapWriter.
  reflexivity.
Qed.
Hint Rewrite @mapWriter_unwrap : cheerios.

Lemma unwrap_s_spec : forall l, unwrap_s (Writer l) = l.
Proof.
  reflexivity.
Qed.

Definition unwrap_d {A : Type} (d : deserializer A) :=
  match d with
  | Deserializer f => f
  end.

Definition bind {A B : Type}
           (d: deserializer A) (f : A -> deserializer B) : deserializer B :=
  Deserializer
    (fun l =>
       match unwrap_d d l with
       | None => None
       | Some (v, l) => unwrap_d (f v) l 
       end).

(* A generic serializer goal solver. The main tactic uses `autorewrite`
   to rewrite repeatedly with all the lemmas in the database above. *)
Ltac cheerios_crush := intros; autorewrite with cheerios; auto.

Definition ret {A : Type} (a : A) : deserializer A :=
  Deserializer (fun l => Some (a, l)).

Definition fmap {A B} (f : A -> B) (d : deserializer A) : deserializer B :=
  bind d (fun a => ret (f a)).

Lemma bind_unwrap : forall A B (m : deserializer A)
                           (f : A -> deserializer B) bin,
    unwrap_d (bind m f) bin = match (unwrap_d m bin) with
                              | None => None
                              | Some (v, bin) => unwrap_d (f v) bin
                              end.
Proof.
  unfold bind.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma ret_unwrap : forall A (x: A) bin, unwrap_d (ret x) bin = Some (x, bin).
Proof.
  reflexivity.
Qed.

Hint Rewrite bind_unwrap  ret_unwrap append_unwrap : cheerios.

Lemma fmap_unwrap: forall A B (f: A -> B) (d: deserializer A)
                          bin, unwrap_d (fmap f d) bin =
                               match (unwrap_d d bin) with
                               | None => None
                               | Some (v, bin) => Some (f v, bin) end.
Proof.
  cheerios_crush.
Qed.

Hint Rewrite fmap_unwrap : cheerios.
(* spec *)

Notation serialize_deserialize_id_monad_spec s d :=
  (forall a (bin : list bool), unwrap_d d (unwrap_s (s a) ++ bin) = Some (a, bin)).

Class Serializer (A : Type) : Type :=
  {
    serialize : A -> writer;
    deserialize : deserializer A;
    serialize_deserialize_id : serialize_deserialize_id_monad_spec serialize deserialize
  }.

Hint Rewrite app_assoc_reverse @serialize_deserialize_id : cheerios.

Lemma serialize_deserialize_id_nil :
  forall A (sA : Serializer A) a,
    unwrap_d deserialize (unwrap_s (serialize a)) = Some (a, []).
Proof.
  intros.
  pose proof serialize_deserialize_id a [].
  rewrite app_nil_r in *.
  apply H.
Qed.

(* basic serializers *)

Definition bool_serialize := putBit.

Definition bool_deserialize : deserializer bool := getBit.

Lemma bool_serialize_deserialize_id :
  serialize_deserialize_id_monad_spec bool_serialize bool_deserialize.
Proof.
  destruct a; auto.
Qed.

Instance bool_Serializer : Serializer bool :=
  {| serialize := bool_serialize;
     deserialize := bool_deserialize;
     serialize_deserialize_id := bool_serialize_deserialize_id
  |}.

(* fold primitive *)

Inductive fold_state S A :=
| Done (a : A)
| More (s : S)
| Error.
Arguments Done {_} {_} _.
Arguments More {_} {_} _.
Arguments Error {_} {_}.

Definition fold {S A}
           (f : bool -> S -> fold_state S A) :=
  fix loop (s : S) (l : list bool) := 
    match l with
    | [] => None
    | b :: l => match f b s with
                | Done a => Some (a, l)
                | More s => loop s l
                | Error => None
                end
    end.

Definition fold_deserializer {S A} f s :=
  Deserializer (fold (f : bool -> S -> fold_state S A) (s : S)).

Lemma fold_unwrap : forall {S A : Type}
                           (f : bool -> S -> fold_state S A) (s : S) l,
    unwrap_d (fold_deserializer f s) l =
    match l with
    | [] => None
    | b :: l => match f b s with
                | Done a => Some (a, l)
                | More s => unwrap_d (fold_deserializer f s) l
                | Error => None
                end
    end.
Proof.
  intros.
  simpl. destruct l; reflexivity.
Qed.

(* positive *)

Fixpoint serialize_positive (p : positive) :=
  match p with
  | xI p => append (append (serialize true) (serialize true))
                   (serialize_positive p)
  | xO p => append (append (serialize true) (serialize false))
                   (serialize_positive p)
  | xH => serialize false
  end.

Definition deserialize_positive_step :=
  fun (b : bool) (s : bool * (positive -> positive)) =>
    match s with
    | (is_digit, k) => if is_digit
                       then More(false, fun p => k ((if b then xI else xO) p))
                       else if b
                            then More(true, k)
                            else Done(k xH)
    end.

Definition deserialize_positive : deserializer positive :=
  fold_deserializer deserialize_positive_step (false, (fun p => p)).

Lemma positive_step : forall (p : positive) (k : positive -> positive) bin,
    fold deserialize_positive_step (false, k)
         (unwrap_s (serialize_positive p) ++ bin)  = Some(k p, bin).
Proof.
  induction p;
    simpl;
    cheerios_crush;
    apply IHp.
Qed.

Theorem serialize_deserialize_positive_id :
  serialize_deserialize_id_monad_spec serialize_positive deserialize_positive.
Proof.
  intros.
  unfold deserialize_positive.
  simpl.
  apply positive_step.
Qed.

Instance positive_Serializer : Serializer positive :=
  {| serialize := serialize_positive;
     deserialize := deserialize_positive;
     serialize_deserialize_id := serialize_deserialize_positive_id
  |}.

(* nat *)

Definition serialize_N n :=
  match n with
  | N0 => serialize false
  | Npos p => append (serialize true) (serialize p)
  end.

Definition deserialize_N :=
  bind (deserialize : deserializer bool)
       (fun b => if b
                 then fmap Npos (deserialize : deserializer positive)
                 else ret N0).

Theorem serialize_deserialize_N_id :
  serialize_deserialize_id_monad_spec serialize_N deserialize_N.
Proof.
  intros.
  destruct a;
    unfold serialize_N, deserialize_N;
    cheerios_crush.
Qed.

Instance N_Serializer : Serializer N :=
  {| serialize := serialize_N;
     deserialize := deserialize_N;
     serialize_deserialize_id := serialize_deserialize_N_id
  |}.

Definition serialize_nat : nat -> writer :=
  mapWriter N.of_nat (serialize : N -> writer).

Definition deserialize_nat : deserializer nat :=
  fmap N.to_nat (deserialize : deserializer N).

Definition serialize_deserialize_nat_id :
  serialize_deserialize_id_monad_spec serialize_nat deserialize_nat.
Proof.
  intros.
  unfold serialize_nat, deserialize_nat.
  cheerios_crush.
  now rewrite Nnat.Nat2N.id.
Qed.

Instance nat_Serializer : Serializer nat :=
  {| serialize := serialize_nat;
     deserialize := deserialize_nat;
     serialize_deserialize_id := serialize_deserialize_nat_id
  |}.

(* basic combinator *)

Section combinators.
  Variables A B : Type.
  Variable sA : Serializer A.
  Variable sB : Serializer B.

  Definition pair_serialize (x : A * B) : writer :=
    let (a, b) := x in append (serialize a) (serialize b).
  
  Definition pair_deserialize {A B : Type}
             (dA: deserializer A) (dB : deserializer B) : deserializer (A * B) :=
    bind dA (fun a => bind dB (fun b => ret (a, b))).

  Lemma serialize_deserialize_pair :
    serialize_deserialize_id_monad_spec pair_serialize
                                        (pair_deserialize deserialize deserialize).
  Proof.
    intros.
    unfold pair_serialize, pair_deserialize.
    destruct a.
    cheerios_crush.
  Qed.

(* option *)
  
  Definition option_serialize (x : option A) : writer :=
    match x with
    | Some a => append (serialize true) (serialize a)
    | None => serialize false
    end.

  Definition option_deserialize : deserializer (option A) :=
    bind deserialize (fun (b : bool) => if b
                                        then fmap (@Some A) deserialize
                                        else ret None).

  Lemma serialize_deserialize_option :
    serialize_deserialize_id_monad_spec option_serialize option_deserialize.
  Proof.
    intros.
    unfold option_serialize, option_deserialize.
    destruct a; cheerios_crush.
  Qed.

(* list *)
  
  Fixpoint list_serialize_rec (l : list A) : writer :=
    match l with
    | [] => empty
    | x :: l => append (serialize x) (list_serialize_rec l)
    end.

  Definition list_serialize l : writer :=
    append (serialize (length l)) (list_serialize_rec l).
  
  Fixpoint list_deserialize_rec (n : nat) : deserializer (list A) :=
    match n with
    | 0 => ret []
    | S n => 
      bind deserialize
           (fun a =>
              (fmap (cons a) (list_deserialize_rec n)))
    end.

  Definition list_deserialize : deserializer (list A) :=
    bind deserialize list_deserialize_rec.

  Lemma serialize_deserialize_list_id_rec :
    forall l bin, unwrap_d (list_deserialize_rec (length l))
                           (unwrap_s (list_serialize_rec l) ++ bin) = Some(l, bin).
  Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl.
      cheerios_crush.
      now rewrite IHl.
  Qed.
  
  Theorem serialize_deserialize_list_id :
    serialize_deserialize_id_monad_spec list_serialize list_deserialize.
  Proof.
    intros.
    unfold list_deserialize, list_serialize.
    cheerios_crush.
    apply serialize_deserialize_list_id_rec.
  Qed.
End combinators.

Inductive binary_tree (A : Type) : Type :=
| Leaf : binary_tree A
| Branch : A -> binary_tree A -> binary_tree A -> binary_tree A.
Arguments Leaf {_}.
Arguments Branch {_} _ _ _.


(* less generalized version of James' n-ary tree serializer *)
Fixpoint serialize_tree_shape (t : binary_tree unit) :=
  let lparen := append (serialize false) (serialize true) in
  let rparen := append (serialize false) (serialize false) in
  match t with
  | Leaf => serialize true
  | Branch _ b1 b2 => append lparen
                             (append (serialize_tree_shape b1)
                                     (append (serialize_tree_shape b2)
                                             rparen))
  end.

Definition serialize_tree_shape_step (b : bool) (s : bool) :=
  @Error bool (binary_tree unit).

Definition deserialize_tree_shape :=
  fold_deserializer serialize_tree_shape_step.

Eval cbv in (serialize_tree_shape
               (Branch tt Leaf Leaf)).
