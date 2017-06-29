Require Import Ascii List ZArith.
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

Definition leastBit (a : ascii) :=
  match a with
  | Ascii b _ _ _ _ _ _ _ => b
  end.          

Definition ascii_eq a b :=
  if ascii_dec a b then true else false.
           
Module Type SERIALIZER.
  Parameter t : Type.
  Parameter empty : t.
  Parameter append : t -> t -> t.
  Parameter putByte : ascii -> t.

  (* For proof only! Do not call from serializers. *)
  Parameter unwrap : t -> list ascii.
  Parameter empty_unwrap : unwrap empty = [].
  Parameter append_unwrap :
      forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Parameter putByte_unwrap : forall (a : ascii), unwrap (putByte a) = [a].
End SERIALIZER.

Module Serializer : SERIALIZER.
  Definition t := list ascii.
  Definition empty : t := [].
  Definition putByte (a : ascii) : t := [a].

  Definition append (x y : t) : t := x ++ y.

  Definition unwrap (x : t) : list ascii := x.

  Lemma empty_unwrap : unwrap empty = [].
  Proof. reflexivity. Qed.

  Lemma putByte_unwrap : forall (a : ascii), unwrap (putByte a) = [a].
  Proof. reflexivity. Qed.

  Lemma append_unwrap :
    forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Proof. reflexivity. Qed.
End Serializer.

Module Type DESERIALIZER.
  Parameter t : Type -> Type.

  Parameter getByte : t ascii.
  Parameter unwrap : forall A, t A -> list ascii -> option (A * list ascii).

  Parameter getByte_unwrap : forall l,
      unwrap getByte l = match l with
                         | [] => None
                         | a :: l => Some (a, l)
                         end.

  Parameter bind : forall A B, t A -> (A -> t B) -> t B.
  Parameter ret : forall A, A -> t A.
  Parameter map : forall A B, (A -> B) -> t A -> t B.

  Parameter fold : forall S A,
      (ascii -> S -> fold_state S A) -> S -> t A.

  Parameter bind_unwrap : forall A B (m : t A)
                             (f : A -> t B) bytes,
      unwrap (bind m f) bytes = match unwrap m bytes with
                                | None => None
                                | Some (v, bytes) => unwrap (f v) bytes
                              end.
  Parameter ret_unwrap : forall A (x: A) bytes, unwrap (ret x) bytes = Some (x, bytes).
  Parameter map_unwrap: forall A B (f: A -> B) (d: t A) bytes,
      unwrap (map f d) bytes =
      match (unwrap d bytes) with
      | None => None
      | Some (v, bytes) => Some (f v, bytes)
      end.

  Parameter fold_unwrap : forall {S A : Type}
                             (f : ascii -> S -> fold_state S A) (s : S) l,
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
  Definition t (A : Type) := list ascii -> option (A * list ascii).
  Definition unwrap {A} (x : t A) := x.

  Definition getByte (l : list ascii) :=
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

  Lemma getByte_unwrap : forall l,
      unwrap getByte l = match l with
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
           (f : ascii -> S -> fold_state S A) (s : S) (l : list ascii) :=
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
                             (f : ascii -> S -> fold_state S A) (s : S) l,
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
     Serializer.empty_unwrap Serializer.putByte_unwrap
     Serializer.append_unwrap Deserializer.getByte_unwrap
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

Lemma serialize_deserialize_ascii_id :
  serialize_deserialize_id_spec Serializer.putByte Deserializer.getByte.
Proof. cheerios_crush. Qed.

Instance ascii_Serializer : Serializer ascii :=
  {| serialize := Serializer.putByte;
     deserialize := Deserializer.getByte;
     serialize_deserialize_id := serialize_deserialize_ascii_id |}.

(* this needs to go here because we need the bool_Serializer instance *)

Lemma fold_append_unwrap :
  forall {S A : Type}
         (f : ascii -> S -> fold_state S A) (s : S)
         (b : ascii) (tail : Serializer.t) (bin : list ascii),
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
         (f : ascii -> S -> fold_state S A) (s : S)
         (b : ascii) (tail : Serializer.t) (bin : list ascii),
    Deserializer.unwrap (Deserializer.fold f s)
                        (Serializer.unwrap (Serializer.append
                                              (Serializer.putByte b)
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

Hint Rewrite @fold_append_unwrap @fold_append_unwrap' : cheerios.

(* positive *)

Inductive le_pos (p : positive) : positive -> Prop :=
| le_p : le_pos p p
| le_xI : forall p2, le_pos p p2 -> le_pos p (xI p2)
| le_xO : forall p2, le_pos p p2 -> le_pos p (xO p2).

Section PositiveInductionPrinciple.
  Variable P : positive -> Prop.

  Lemma strongind_pos_aux :
    P xH ->
    (forall q, ((forall p, le_pos p q -> P p) -> P (xI q)) /\
               ((forall p, le_pos p q -> P p) -> P (xO q))) ->
    (forall q, (forall p, le_pos p q -> P p)).
  Proof.
    induction q;
      intros;
      inversion H1;
      auto;
      apply H0;
      apply IHq.
  Qed.

  Lemma weaken_pos :
    (forall q, (forall p, le_pos p q -> P p)) -> forall p, P p.
  Proof.
    intros.
    apply (H p p).
    constructor.
  Qed.

  Theorem strongind_pos :
    P xH ->
    (forall q, ((forall p, le_pos p q -> P p) -> P (xI q)) /\
               ((forall p, le_pos p q -> P p) -> P (xO q))) ->
    forall p, P p.
  Proof.
    intros.
    apply weaken_pos.
    now apply strongind_pos_aux.
  Qed.
End PositiveInductionPrinciple.

Local Open Scope char_scope.

Fixpoint serialize_positive p :=
  match p with
  | xI (xI (xI p)) => Serializer.append (serialize "014")
                                        (serialize_positive p)
  | xI (xI (xO p)) => Serializer.append (serialize "013")
                                        (serialize_positive p)
  | xI (xO (xI p)) => Serializer.append (serialize "012")
                                        (serialize_positive p)
  | xI (xO (xO p)) => Serializer.append (serialize "011")
                                        (serialize_positive p)
  | xO (xI (xI p)) => Serializer.append (serialize "010")
                                        (serialize_positive p)
  | xO (xI (xO p)) => Serializer.append (serialize "009")
                                        (serialize_positive p)
  | xO (xO (xI p)) => Serializer.append (serialize "008")
                                        (serialize_positive p)
  | xO (xO (xO p)) => Serializer.append (serialize "007")
                                        (serialize_positive p)
  | xI (xI p) => Serializer.append (serialize "006")
                                   (serialize_positive p)
  | xI (xO p) => Serializer.append (serialize "005")
                                   (serialize_positive p)
  | xO (xI p) => Serializer.append (serialize "004")
                                   (serialize_positive p)
  | xO (xO p) => Serializer.append (serialize "003")
                                   (serialize_positive p)
  | xI p => Serializer.append (serialize "002")
                              (serialize_positive p)
  | xO p => Serializer.append (serialize "001")
                              (serialize_positive p)
  | XH => serialize "000"
  end.

Definition deserialize_positive_step
           (b : ascii)
           (s : positive -> positive) := 
  if ascii_eq b "014"
  then More (fun p => s (xI (xI (xI p))))
  else if ascii_eq b "013"
       then More (fun p => s (xI (xI (xO p))))
       else if ascii_eq b "012"
            then More (fun p => s (xI (xO (xI p))))
            else if ascii_eq b "011"
                 then More (fun p => s (xI (xO (xO p))))
                 else if ascii_eq b "010"
                      then More (fun p => s (xO (xI (xI p))))
                      else if ascii_eq b "009"
                           then More (fun p => s (xO (xI (xO p))))
                           else if ascii_eq b "008"
                                then More (fun p => s (xO (xO (xI p))))
                                else if ascii_eq b "007"
                                     then More (fun p => s (xO (xO (xO p))))
                                     else if ascii_eq b "006"
                                          then More (fun p => s (xI (xI p)))
                                          else if ascii_eq b "005"
                                               then More (fun p => s (xI (xO p)))
                                               else if ascii_eq b "004"
                                                    then More (fun p => s (xO (xI p)))
                                                    else if ascii_eq b "003"
                                                         then More (fun p => s (xO (xO p)))
                                                         else if ascii_eq b "002"
                                                              then More (fun p => s (xI p))
                                                              else if ascii_eq b "001"
                                                                   then More (fun p => s (xO p))
                                                                   else if ascii_eq b "000"
                                                                        then Done (s xH)
                                                                        else Error.

Definition positive_step_aux p :=
  forall (k : positive -> positive) (bytes : list ascii),
    Deserializer.unwrap (Deserializer.fold deserialize_positive_step k)
                        (Serializer.unwrap (serialize_positive p) ++ bytes)
    = Some(k p, bytes).

Lemma positive_step :
  forall (p : positive), positive_step_aux p.
Proof.
  apply strongind_pos; unfold positive_step_aux.
  - unfold serialize_positive.
    cheerios_crush.
  - split;
      intros;
      try destruct q;
      try destruct q;
      simpl; cheerios_crush; simpl; rewrite H || cheerios_crush;
        try reflexivity;
        repeat constructor.
Qed.

Definition deserialize_positive :=
  Deserializer.fold deserialize_positive_step (fun p => p).

Theorem serialize_deserialize_positive_id :
  serialize_deserialize_id_spec serialize_positive
                                deserialize_positive.
Proof.
  intros.
  unfold deserialize_positive.
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
  | N0 => serialize zero
  | Npos p => Serializer.append (serialize one) (serialize p)
  end.

Definition deserialize_N :=
  Deserializer.bind deserialize
                    (fun (b : ascii) => if leastBit b
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
Check Nnat.Nat2N.id.

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
    | Some a => Serializer.append (serialize one) (serialize a)
    | None => serialize zero
    end.

  Definition option_deserialize : Deserializer.t (option A) :=
    Deserializer.bind deserialize
                      (fun (b : ascii) =>
                         if leastBit b
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
  match t with
  | Leaf => Serializer.empty
  | Branch _ b1 b2 =>
    Serializer.append (serialize "(")
                      (Serializer.append (serialize_tree_shape b1)
                                         (Serializer.append (serialize_tree_shape b2)
                                                        (serialize ")")))
  end.

Definition serialize_tree_shape_step (b : ascii) (s : bool) :=
  @Error bool (binary_tree unit).

Definition deserialize_tree_shape :=
  Deserializer.fold serialize_tree_shape_step.

Eval cbv in (serialize_tree_shape
               (Branch tt Leaf Leaf)).

Extract Inlined Constant
        Serializer.t => "Serializer_primitives.serializer".
Extract Constant
        Deserializer.t "'a"  => "Serializer_primitives.deserializer".
Extraction Inline Deserializer.t.
Extract Inductive fold_state => "Serializer_primitives.fold_state"
                                  ["Serializer_primitives.Done"
                                     "Serializer_primitives.More"
                                     "Serializer_primitives.Error"].
Extract Inlined Constant Serializer.putByte => "Serializer_primitives.putByte".
Extract Inlined Constant Serializer.empty => "Serializer_primitives.empty".
Extract Inlined Constant Serializer.append => "Serializer_primitives.append".
Extract Inlined Constant Deserializer.bind => "Serializer_primitives.bind".
Extract Inlined Constant Deserializer.getByte => "Serializer_primitives.getByte".
Extract Inlined Constant Deserializer.map => "Serializer_primitives.map".
Extract Inlined Constant Deserializer.ret => "Serializer_primitives.ret".
Extract Inlined Constant Deserializer.fold => "Serializer_primitives.fold".

Extract Inlined Constant Serializer.empty_unwrap => "Obj.magic".
Extract Inlined Constant Serializer.putByte_unwrap => "Obj.magic".
Extract Inlined Constant Serializer.append_unwrap => "Obj.magic".

Extract Inlined Constant Deserializer.getByte_unwrap => "Obj.magic".
Extract Inlined Constant Deserializer.bind_unwrap => "Obj.magic".
Extract Inlined Constant Deserializer.ret_unwrap => "Obj.magic".
Extract Inlined Constant Deserializer.map_unwrap => "Obj.magic".
Extract Inlined Constant Deserializer.fold_unwrap => "Obj.magic".

Extract Inlined Constant Serializer.unwrap => "Obj.magic".
Extract Inlined Constant Deserializer.unwrap => "Obj.magic".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction "ocaml-cheerios/positive_extracted.ml"
           serialize_positive deserialize_positive.