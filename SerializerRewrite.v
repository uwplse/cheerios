
Require Import List ZArith.
Import ListNotations.
Set Implicit Arguments.

(* writer primitives *)
Inductive fold_state S A :=
| Done (a : A)
| More (s : S)
| Error.
Arguments Done {_} {_} _.
Arguments More {_} {_} _.
Arguments Error {_} {_}.

Module Type SERIALIZER.
  Parameter t : Type.
  Parameter empty : t.
  Parameter append : t -> t -> t.
  Parameter putBit : bool -> t.

  (* For proof only! Do not call from serializers. *)
  Parameter unwrap : t -> list bool.
  (* Now we have one unwrap lemma per primitive operation from above. *)
  Parameter empty_unwrap : unwrap empty = [].
  Parameter append_unwrap :
      forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Parameter putBit_unwrap : forall (b : bool), unwrap (putBit b) = [b].
End SERIALIZER.

(* Now we can rejigger our current implementation to implement this signature.
  By explicitly ascribing the signature with `:`, we "seal" the module, so no
  implementation details are accessible elsewhere. *)

Module Serializer : SERIALIZER.
  (* We could also use a "wrapper" inductive type here,
     but there's no real point to doing so. *)
  Definition t := list bool.
  Definition empty : t := [].
  Definition putBit (b : bool) : t := [b].

  Definition append (x y : t) : t := x ++ y.

  Definition unwrap (x : t) : list bool := x.

  Lemma empty_unwrap : unwrap empty = [].
  Proof. reflexivity. Qed.

  Lemma putBit_unwrap : forall (b : bool), unwrap (putBit b) = [b].
  Proof. reflexivity. Qed.

  Lemma append_unwrap :
    forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Proof. reflexivity. Qed.
End Serializer.

Module Type DESERIALIZER.
  Parameter t : Type -> Type.

  Parameter getBit : t bool.
  Parameter unwrap : forall A, t A -> list bool -> option (A * list bool).

  Parameter getBit_unwrap : forall l,
      unwrap getBit l = match l with
                               | [] => None
                               | b :: l => Some (b, l)
                        end.
  Parameter bind : forall A B, t A -> (A -> t B) -> t B.
  Parameter ret : forall A, A -> t A.
  Parameter map : forall A B, (A -> B) -> t A -> t B.
  Parameter fold : forall S A,
      (bool -> S -> fold_state S A) -> S -> t A.

  Parameter bind_unwrap : forall A B (m : t A)
                             (f : A -> t B) bin,
      unwrap (bind m f) bin = match unwrap m bin with
                                | None => None
                                | Some (v, bin) => unwrap (f v) bin
                              end.
  Parameter ret_unwrap : forall A (x: A) bin, unwrap (ret x) bin = Some (x, bin).
  Parameter map_unwrap: forall A B (f: A -> B) (d: t A) bin,
      unwrap (map f d) bin =
      match (unwrap d bin) with
      | None => None
      | Some (v, bin) => Some (f v, bin)
      end.

  Parameter fold_unwrap : forall {S A : Type}
                             (f : bool -> S -> fold_state S A) (s : S) l,
      unwrap (fold f s) l =
      match l with
      | [] => None
      | b :: l => match f b s with
                  | Done a => Some (a, l)
                  | More s => unwrap (fold f s) l
                  | Error => None
                  end
      end.
End DESERIALIZER.

Module Deserializer : DESERIALIZER.
  Definition t (A : Type) := list bool -> option (A * list bool).
  Definition unwrap {A} (x : t A) := x.

  Definition getBit (l : list bool) :=
    match l with
    | [] => None
    | b :: l => Some (b, l)
    end.

  Definition bind {A B} (d: t A) (f : A -> t B) : t B :=
    fun l =>
      match unwrap d l with
      | None => None
      | Some (v, l) => unwrap (f v) l 
      end.

  Definition ret {A} (a : A) : t A :=
    fun l => Some (a, l).

  Definition map {A B} (f : A -> B) (d : t A) : t B :=
    bind d (fun a => ret (f a)).

  Lemma getBit_unwrap : forall l,
      unwrap getBit l = match l with
                        | [] => None
                        | b :: l => Some (b, l)
                        end.
  Proof. reflexivity. Qed.

  Lemma bind_unwrap : forall A B (m : t A)
                             (f : A -> t B) bin,
      unwrap (bind m f) bin = match unwrap m bin with
                                | None => None
                                | Some (v, bin) => unwrap (f v) bin
                                end.
  Proof.
    unfold bind. 
    intros.
    reflexivity.
  Qed.

  Fixpoint fold {S A}
           (f : bool -> S -> fold_state S A) (s : S) (l : list bool) :=
    match l with
    | [] => None
    | b :: l => match f b s with
                | Done a => Some (a, l)
                | More s => fold f s l
                | Error => None
                end
    end.

  Lemma ret_unwrap : forall A (x: A) bin, unwrap (ret x) bin = Some (x, bin).
  Proof. reflexivity. Qed.

  Lemma map_unwrap: forall A B (f: A -> B) (d: t A) bin,
      unwrap (map f d) bin =
      match (unwrap d bin) with
      | None => None
      | Some (v, bin) => Some (f v, bin)
      end.
  Proof. reflexivity. Qed.
  Lemma fold_unwrap : forall {S A : Type}
                             (f : bool -> S -> fold_state S A) (s : S) l,
      unwrap (fold f s) l =
      match l with
      | [] => None
      | b :: l => match f b s with
                  | Done a => Some (a, l)
                  | More s => unwrap (fold f s) l
                  | Error => None
                  end
      end.
  Proof.
    intros.
    simpl. destruct l; reflexivity.
  Qed.
End Deserializer.
    
Notation serialize_deserialize_id_spec s d :=
  (forall a bin,
      Deserializer.unwrap d (Serializer.unwrap (s a) ++ bin) = Some(a, bin)).

Ltac cheerios_crush := intros; autorewrite with cheerios; auto.

Hint Rewrite app_ass 
     Serializer.empty_unwrap Serializer.putBit_unwrap
     Serializer.append_unwrap Deserializer.getBit_unwrap
     Deserializer.bind_unwrap Deserializer.ret_unwrap
     Deserializer.map_unwrap @Deserializer.fold_unwrap : cheerios.

Class Serializer (A : Type) : Type :=
  {
    serialize : A -> Serializer.t;
    deserialize : Deserializer.t A;
    serialize_deserialize_id : serialize_deserialize_id_spec serialize deserialize
  }.
Hint Rewrite @serialize_deserialize_id : cheerios.

Lemma serialize_deserialize_id_nil :
  forall A (sA : Serializer A) a,
    Deserializer.unwrap deserialize (Serializer.unwrap (serialize a)) = Some (a, []).
Proof.
  intros.
  pose proof serialize_deserialize_id a [].
  rewrite app_nil_r in *.
  apply H.
Qed.

(* basic serializers *)

Lemma bool_serialize_deserialize_id :
  serialize_deserialize_id_spec Serializer.putBit Deserializer.getBit.
Proof.
  destruct a;
    cheerios_crush.
Qed.

Instance bool_Serializer : Serializer bool :=
  {| serialize := Serializer.putBit;
     deserialize := Deserializer.getBit;
     serialize_deserialize_id := bool_serialize_deserialize_id
  |}.

(* this needs to go here because we need the bool_Serializer instance *)

Lemma fold_append_unwrap :
  forall {S A : Type}
         (f : bool -> S -> fold_state S A) (s : S)
         (b : bool) (tail : Serializer.t) (bin : list bool),
    Deserializer.unwrap (Deserializer.fold f s)
                        (Serializer.unwrap (Serializer.append
                                              (serialize b)
                                              tail) ++ bin) =
    match f b s with
    | Done a => Some(a, Serializer.unwrap tail ++ bin)
    | More s => Deserializer.unwrap (Deserializer.fold f s)
                                    (Serializer.unwrap tail ++ bin)
    | Error => None
    end.
Proof.
  cheerios_crush.
Qed.

Lemma fold_append_unwrap' :
  forall {S A : Type}
         (f : bool -> S -> fold_state S A) (s : S)
         (b : bool) (tail : Serializer.t) (bin : list bool),
    Deserializer.unwrap (Deserializer.fold f s)
                        (Serializer.unwrap (Serializer.append
                                              (Serializer.putBit b)
                                              tail) ++ bin) =
    match f b s with
    | Done a => Some(a, Serializer.unwrap tail ++ bin)
    | More s => Deserializer.unwrap (Deserializer.fold f s)
                                    (Serializer.unwrap tail ++ bin)
    | Error => None
    end.
Proof.
  cheerios_crush.
Qed.

(* positive *)

Fixpoint serialize_positive (p : positive) : Serializer.t :=
  match p with
  | xI p => Serializer.append (serialize true)
                              (Serializer.append (serialize true)
                                                 (serialize_positive p))
  | xO p => Serializer.append  (serialize true)
                               (Serializer.append (serialize false)
                                                  (serialize_positive p))
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

Hint Rewrite @fold_append_unwrap @fold_append_unwrap' : cheerios.

Definition deserialize_positive : Deserializer.t positive :=
  Deserializer.fold deserialize_positive_step (false, (fun p => p)).

Lemma positive_step : forall (p : positive) (k : positive -> positive) (bin : list bool),
    Deserializer.unwrap (Deserializer.fold deserialize_positive_step (false, k))
         (Serializer.unwrap (serialize_positive p) ++ bin)  = Some(k p, bin).
Proof.
  induction p;
    intros;
    unfold serialize_positive;
    fold serialize_positive;
    repeat (cheerios_crush; simpl; try (now rewrite IHp)).
Qed.

Theorem serialize_deserialize_positive_id :
  serialize_deserialize_id_spec serialize_positive deserialize_positive.
Proof.
  intros.
  unfold deserialize_positive.
  simpl.
  apply positive_step.
Qed.

Instance positive_Serializer : Serializer positive.
Proof.
  exact ({| serialize := serialize_positive;
     deserialize := deserialize_positive;
     serialize_deserialize_id := serialize_deserialize_positive_id
         |}).
Qed.

(* nat *)

Definition serialize_N n :=
  match n with
  | N0 => serialize false
  | Npos p => Serializer.append (serialize true) (serialize p)
  end.

Definition deserialize_N :=
  Deserializer.bind deserialize
                    (fun (b : bool) => if b
                                       then Deserializer.map Npos deserialize
                                       else Deserializer.ret N0).

Theorem serialize_deserialize_N_id :
  serialize_deserialize_id_spec serialize_N deserialize_N.
Proof.
  intros.
  unfold serialize_N, deserialize_N.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance N_Serializer : Serializer N :=
  {| serialize := serialize_N;
     deserialize := deserialize_N;
     serialize_deserialize_id := serialize_deserialize_N_id
  |}.

Definition serialize_nat n : Serializer.t :=
  serialize (N.of_nat n).

Definition deserialize_nat : Deserializer.t nat :=
  Deserializer.map N.to_nat deserialize.

Definition serialize_deserialize_nat_id :
  serialize_deserialize_id_spec serialize_nat deserialize_nat.
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

  Definition pair_serialize (x : A * B) : Serializer.t :=
    let (a, b) := x in Serializer.append (serialize a) (serialize b).
  
  Definition pair_deserialize : Deserializer.t (A * B) :=
    Deserializer.bind deserialize
                      (fun (a : A) =>
                         Deserializer.bind deserialize
                                           (fun b =>
                                              Deserializer.ret (a, b))).

  Lemma serialize_deserialize_pair_id :
    serialize_deserialize_id_spec pair_serialize pair_deserialize.
  Proof.
    intros.
    unfold pair_serialize, pair_deserialize.
    destruct a.
    cheerios_crush.
  Qed.

  Global Instance pair_Serializer : Serializer (A * B) :=
    {| serialize := pair_serialize;
     deserialize := pair_deserialize;
     serialize_deserialize_id := serialize_deserialize_pair_id |}.
  
(* option *)
  
  Definition option_serialize (x : option A) : Serializer.t :=
    match x with
    | Some a => Serializer.append (serialize true) (serialize a)
    | None => serialize false
    end.

  Definition option_deserialize : Deserializer.t (option A) :=
    Deserializer.bind deserialize
                      (fun (b : bool) =>
                         if b
                         then Deserializer.map (@Some A) deserialize
                         else Deserializer.ret None).

  Lemma serialize_deserialize_option :
    serialize_deserialize_id_spec option_serialize option_deserialize.
  Proof.
    intros.
    unfold option_serialize, option_deserialize.
    destruct a;
      repeat (cheerios_crush; simpl).
  Qed.

(* list *)
  
  Fixpoint list_serialize_rec (l : list A) : Serializer.t :=
    match l with
    | [] => Serializer.empty
    | x :: l => Serializer.append (serialize x) (list_serialize_rec l)
    end.

  Definition list_serialize l : Serializer.t :=
    Serializer.append (serialize (length l)) (list_serialize_rec l).
  
  Fixpoint list_deserialize_rec (n : nat) : Deserializer.t (list A) :=
    match n with
    | 0 => Deserializer.ret []
    | S n => 
      Deserializer.bind deserialize
           (fun a =>
              (Deserializer.map (cons a) (list_deserialize_rec n)))
    end.

  Definition list_deserialize : Deserializer.t (list A) :=
    Deserializer.bind deserialize list_deserialize_rec.

  Lemma serialize_deserialize_list_id_rec :
    forall l bin, Deserializer.unwrap (list_deserialize_rec (length l))
                                      (Serializer.unwrap (list_serialize_rec l) ++ bin)
                  = Some(l, bin).
  Proof.
    intros.
    induction l;
      simpl;
      cheerios_crush;
      now rewrite IHl.
  Qed.
  
  Theorem serialize_deserialize_list_id :
    serialize_deserialize_id_spec list_serialize list_deserialize.
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
  let lparen := Serializer.append (serialize false) (serialize true) in
  let rparen := Serializer.append (serialize false) (serialize false) in
  match t with
  | Leaf => serialize true
  | Branch _ b1 b2 => Serializer.append lparen
                             (Serializer.append (serialize_tree_shape b1)
                                     (Serializer.append (serialize_tree_shape b2)
                                                        rparen))
  end.

Definition serialize_tree_shape_step (b : bool) (s : bool) :=
  @Error bool (binary_tree unit).

Definition deserialize_tree_shape :=
  Deserializer.fold serialize_tree_shape_step.

Eval cbv in (serialize_tree_shape
               (Branch tt Leaf Leaf)).

Extract Constant Serializer.t => "Serializer_primitives.serializer".
Extract Constant Deserializer.t "'a"  => "'a Serializer_primitives.deserializer".
Extract Inductive fold_state => "Serializer_primitives.fold_state"
                                  ["Serializer_primitives.Done"
                                     "Serializer_primitives.More"
                                     "Serializer_primitives.Error"].
Extract Constant Serializer.putBit => "Serializer_primitives.putBit".
Extract Constant Serializer.empty => "Serializer_primitives.empty".
Extract Constant Serializer.append => "Serializer_primitives.append".
Extract Constant Deserializer.bind => "Serializer_primitives.bind".
Extract Constant Deserializer.getBit => "Serializer_primitives.getBit".
Extract Constant Deserializer.ret => "Serializer_primitives.ret".
Extract Constant Deserializer.fold => "Serializer_primitives.fold".

Extract Constant Serializer.unwrap => "Obj.magic".
Extract Constant Deserializer.unwrap => "Obj.magic".

Require Import ExtrOcamlBasic.

Definition bool_pair_serialize (b1 b2 : bool) := serialize (b1, b2).

Extraction "ocaml-cheerios/BoolPair.ml" bool_pair_serialize.