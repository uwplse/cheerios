(*

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

Inductive byte :=
| x00 | x01 | x02 | x03 | x04 | x05 | x06 | x07 | x08 | x09 | x0a | x0b | x0c
| x0d | x0e | x0f | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19
| x1a | x1b | x1c | x1d | x1e | x1f | x20 | x21 | x22 | x23 | x24 | x25 | x26 
| x27 | x28 | x29 | x2a | x2b | x2c | x2d | x2e | x2f | x30 | x31 | x32 | x33 
| x34 | x35 | x36 | x37 | x38 | x39 | x3a | x3b | x3c | x3d | x3e | x3f | x40 
| x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c | x4d 
| x4e | x4f | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58 | x59 | x5a 
| x5b | x5c | x5d | x5e | x5f | x60 | x61 | x62 | x63 | x64 | x65 | x66 | x67 
| x68 | x69 | x6a | x6b | x6c | x6d | x6e | x6f | x70 | x71 | x72 | x73 | x74 
| x75 | x76 | x77 | x78 | x79 | x7a | x7b | x7c | x7d | x7e | x7f | x80 | x81 
| x82 | x83 | x84 | x85 | x86 | x87 | x88 | x89 | x8a | x8b | x8c | x8d | x8e 
| x8f | x90 | x91 | x92 | x93 | x94 | x95 | x96 | x97 | x98 | x99 | x9a | x9b 
| x9c | x9d | x9e | x9f | xa0 | xa1 | xa2 | xa3 | xa4 | xa5 | xa6 | xa7 | xa8 
| xa9 | xaa | xab | xac | xad | xae | xaf | xb0 | xb1 | xb2 | xb3 | xb4 | xb5 
| xb6 | xb7 | xb8 | xb9 | xba | xbb | xbc | xbd | xbe | xbf | xc0 | xc1 | xc2 
| xc3 | xc4 | xc5 | xc6 | xc7 | xc8 | xc9 | xca | xcb | xcc | xcd | xce | xcf 
| xd0 | xd1 | xd2 | xd3 | xd4 | xd5 | xd6 | xd7 | xd8 | xd9 | xda | xdb | xdc 
| xdd | xde | xdf | xe0 | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9 
| xea | xeb | xec | xed | xee | xef | xf0 | xf1 | xf2 | xf3 | xf4 | xf5 | xf6 
| xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff.

Definition leastBit (a : ascii) :=
  match a with
  | Ascii b _ _ _ _ _ _ _ => b
  end.          

Module Type SERIALIZER.
  Parameter t : Type.
  Parameter empty : t.
  Parameter append : t -> t -> t.
  Parameter putByte : byte -> t.

  (* For proof only! Do not call from serializers. *)
  Parameter unwrap : t -> list byte.
  Parameter empty_unwrap : unwrap empty = [].
  Parameter append_unwrap :
      forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Parameter putByte_unwrap : forall (a : byte), unwrap (putByte a) = [a].
End SERIALIZER.

Module Serializer : SERIALIZER.
  Definition t := list byte.
  Definition empty : t := [].
  Definition putByte (a : byte) : t := [a].

  Definition append (x y : t) : t := x ++ y.

  Definition unwrap (x : t) : list byte := x.

  Lemma empty_unwrap : unwrap empty = [].
  Proof. reflexivity. Qed.

  Lemma putByte_unwrap : forall (a : byte), unwrap (putByte a) = [a].
  Proof. reflexivity. Qed.

  Lemma append_unwrap :
    forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Proof. reflexivity. Qed.
End Serializer.

Module Type DESERIALIZER.
  Parameter t : Type -> Type.

  Parameter getByte : t byte.
  Parameter unwrap : forall A, t A -> list byte -> option (A * list byte).

  Parameter getByte_unwrap : forall l,
      unwrap getByte l = match l with
                         | [] => None
                         | a :: l => Some (a, l)
                         end.

  Parameter bind : forall A B, t A -> (A -> t B) -> t B.
  Parameter ret : forall A, A -> t A.
  Parameter fail : forall A, t A.
  Parameter map : forall A B, (A -> B) -> t A -> t B.

  Parameter fold : forall S A,
      (byte -> S -> fold_state S A) -> S -> t A.

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
                             (f : byte -> S -> fold_state S A) (s : S) l,
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

Instance byte_Serializer : Serializer byte :=
  {| serialize := Serializer.putByte;
     deserialize := Deserializer.getByte;
     serialize_deserialize_id := serialize_deserialize_ascii_id |}.

(* this needs to go here because we need the bool_Serializer instance *)

Lemma fold_append_unwrap :
  forall {S A : Type}
         (f : byte -> S -> fold_state S A) (s : S)
         (b : byte) (tail : Serializer.t) (bin : list byte),
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
         (f : byte -> S -> fold_state S A) (s : S)
         (b : byte) (tail : Serializer.t) (bin : list byte),
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
  | xI (xI (xI p)) => Serializer.append (serialize x0e)
                                        (serialize_positive p)
  | xI (xI (xO p)) => Serializer.append (serialize x0d)
                                        (serialize_positive p)
  | xI (xO (xI p)) => Serializer.append (serialize x0c)
                                        (serialize_positive p)
  | xI (xO (xO p)) => Serializer.append (serialize x0b)
                                        (serialize_positive p)
  | xO (xI (xI p)) => Serializer.append (serialize x0a)
                                        (serialize_positive p)
  | xO (xI (xO p)) => Serializer.append (serialize x09)
                                        (serialize_positive p)
  | xO (xO (xI p)) => Serializer.append (serialize x08)
                                        (serialize_positive p)
  | xO (xO (xO p)) => Serializer.append (serialize x07)
                                        (serialize_positive p)
  | xI (xI p) => Serializer.append (serialize x06)
                                   (serialize_positive p)
  | xI (xO p) => Serializer.append (serialize x05)
                                   (serialize_positive p)
  | xO (xI p) => Serializer.append (serialize x04)
                                   (serialize_positive p)
  | xO (xO p) => Serializer.append (serialize x03)
                                   (serialize_positive p)
  | xI p => Serializer.append (serialize x02)
                              (serialize_positive p)
  | xO p => Serializer.append (serialize x01)
                              (serialize_positive p)
  | XH => serialize x00
  end.

Definition deserialize_positive_step
           (b : byte)
           (s : positive -> positive) := 
  match b with
  | x0e => More (fun p => s (xI (xI (xI p))))
  | x0d => More (fun p => s (xI (xI (xO p))))
  | x0c => More (fun p => s (xI (xO (xI p))))
  | x0b => More (fun p => s (xI (xO (xO p))))
  | x0a => More (fun p => s (xO (xI (xI p))))
  | x09 => More (fun p => s (xO (xI (xO p))))
  | x08 => More (fun p =>  s (xO (xO (xI p))))
  | x07 => More (fun p => s (xO (xO (xO p))))
  | x06 => More (fun p => s (xI (xI p)))
  | x05 => More (fun p => s (xI (xO p)))
  | x04 => More (fun p => s (xO (xI p)))
  | x03 => More (fun p => s (xO (xO p)))
  | x02 => More (fun p => s (xI p))
  | x01 => More (fun p => s (xO p))
  | x00 => Done (s xH)
  | _ => Error
  end.

Definition positive_step_aux p :=
  forall (k : positive -> positive) (bytes : list byte),
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
  | N0 => serialize x00
  | Npos p => Serializer.append (serialize x01) (serialize p)
  end.

Definition deserialize_N :=
  Deserializer.bind deserialize
                    (fun (b : byte) => match b with
                                       | x00 => Deserializer.ret N0
                                       | x01 => Deserializer.map Npos deserialize
                                       | _ => Deserializer.error
                                       end).

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
    | Some a => Serializer.append (serialize x01) (serialize a)
    | None => serialize x00
    end.

  Definition option_deserialize : Deserializer.t (option A) :=
    Deserializer.bind deserialize
                      (fun (b : byte) =>
                         match b with
                         | x01 => Deserializer.map (@Some A) deserialize
                         | x00 => Deserializer.ret None
                         | _ => Deserializer.error
                         end).

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
    Serializer.append (serialize x00)
                      (Serializer.append (serialize_tree_shape b1)
                                         (Serializer.append (serialize_tree_shape b2)
                                                        (serialize x01)))
  end.

Definition serialize_tree_shape_step (b : byte) (s : bool) :=
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

Extract Inductive byte =>
"char"
  ["'\000'" "'\001'" "'\002'" "'\003'" "'\004'" "'\005'" "'\006'" "'\007'" "'\008'" "'\009'" "'\010'" "'\011'" "'\012'" "'\013'" "'\014'" "'\015'" "'\016'" "'\017'" "'\018'" "'\019'" "'\020'" "'\021'" "'\022'" "'\023'" "'\024'" "'\025'" "'\026'" "'\027'" "'\028'" "'\029'" "'\030'" "'\031'" "'\032'" "'\033'" "'\034'" "'\035'" "'\036'" "'\037'" "'\038'" "'\039'" "'\040'" "'\041'" "'\042'" "'\043'" "'\044'" "'\045'" "'\046'" "'\047'" "'\048'" "'\049'" "'\050'" "'\051'" "'\052'" "'\053'" "'\054'" "'\055'" "'\056'" "'\057'" "'\058'" "'\059'" "'\060'" "'\061'" "'\062'" "'\063'" "'\064'" "'\065'" "'\066'" "'\067'" "'\068'" "'\069'" "'\070'" "'\071'" "'\072'" "'\073'" "'\074'" "'\075'" "'\076'" "'\077'" "'\078'" "'\079'" "'\080'" "'\081'" "'\082'" "'\083'" "'\084'" "'\085'" "'\086'" "'\087'" "'\088'" "'\089'" "'\090'" "'\091'" "'\092'" "'\093'" "'\094'" "'\095'" "'\096'" "'\097'" "'\098'" "'\099'" "'\100'" "'\101'" "'\102'" "'\103'" "'\104'" "'\105'" "'\106'" "'\107'" "'\108'" "'\109'" "'\110'" "'\111'" "'\112'" "'\113'" "'\114'" "'\115'" "'\116'" "'\117'" "'\118'" "'\119'" "'\120'" "'\121'" "'\122'" "'\123'" "'\124'" "'\125'" "'\126'" "'\127'" "'\128'" "'\129'" "'\130'" "'\131'" "'\132'" "'\133'" "'\134'" "'\135'" "'\136'" "'\137'" "'\138'" "'\139'" "'\140'" "'\141'" "'\142'" "'\143'" "'\144'" "'\145'" "'\146'" "'\147'" "'\148'" "'\149'" "'\150'" "'\151'" "'\152'" "'\153'" "'\154'" "'\155'" "'\156'" "'\157'" "'\158'" "'\159'" "'\160'" "'\161'" "'\162'" "'\163'" "'\164'" "'\165'" "'\166'" "'\167'" "'\168'" "'\169'" "'\170'" "'\171'" "'\172'" "'\173'" "'\174'" "'\175'" "'\176'" "'\177'" "'\178'" "'\179'" "'\180'" "'\181'" "'\182'" "'\183'" "'\184'" "'\185'" "'\186'" "'\187'" "'\188'" "'\189'" "'\190'" "'\191'" "'\192'" "'\193'" "'\194'" "'\195'" "'\196'" "'\197'" "'\198'" "'\199'" "'\200'" "'\201'" "'\202'" "'\203'" "'\204'" "'\205'" "'\206'" "'\207'" "'\208'" "'\209'" "'\210'" "'\211'" "'\212'" "'\213'" "'\214'" "'\215'" "'\216'" "'\217'" "'\218'" "'\219'" "'\220'" "'\221'" "'\222'" "'\223'" "'\224'" "'\225'" "'\226'" "'\227'" "'\228'" "'\229'" "'\230'" "'\231'" "'\232'" "'\233'" "'\234'" "'\235'" "'\236'" "'\237'" "'\238'" "'\239'" "'\240'" "'\241'" "'\242'" "'\243'" "'\244'" "'\245'" "'\246'" "'\247'" "'\248'" "'\249'" "'\250'" "'\251'" "'\252'" "'\253'" "'\254'" "'\255'" ].

Extract Inlined Constant Serializer.putByte => "Serializer_primitives.putByte".
Extract Inlined Constant Serializer.empty => "Serializer_primitives.empty".
Extract Inlined Constant Serializer.append => "Serializer_primitives.append".

Extract Inlined Constant Deserializer.getByte => "Serializer_primitives.getByte".
Extract Inlined Constant Deserializer.bind => "Serializer_primitives.bind".
Extract Inlined Constant Deserializer.error => "Serializer_primitives.fail".
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

*)