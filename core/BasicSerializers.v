Require Import List ZArith.
Import ListNotations.

From StructTact Require Import StructTactics Fin.
Require Fin Ascii.

Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Tactics.
Require Import Cheerios.Types.
Require Import Cheerios.IOStream.

Module Type BASICSERIALIZERS (Writer : WRITER) (Reader : READER).
  Module RWClass := SerializerClass Writer Reader.
  Export RWClass.
  
  Parameter byte_Serializer : RWClass.Serializer byte.
  Parameter bool_Serializer : RWClass.Serializer bool.
  Parameter ascii_Serializer : RWClass.Serializer Ascii.ascii.

  Parameter positive_Serializer : RWClass.Serializer positive.
  Parameter nat_Serializer : RWClass.Serializer nat.

  Parameter byte_unwrap : forall b : byte, Writer.unwrap (serialize b) = [b].
End BASICSERIALIZERS.

Module BasicSerializers (Writer : WRITER) (Reader : READER) :
  BASICSERIALIZERS Writer Reader.
  Module SerializerClass := SerializerClass Writer Reader.
  Module RWClass := SerializerClass.
  Import SerializerClass.

  Module WRewrite := WriterRewrite Writer.
  Module RRewrite := ReaderRewrite Reader.
  Import WRewrite.
  Import RRewrite.

  Module DeserializerMonad := DeserializerMonad Reader.
  Import DeserializerMonad.
  Import DeserializerNotations.
  
  Lemma byte_serialize_deserialize_id :
    serialize_deserialize_id_spec Writer.putByte Reader.getByte.
  Proof. cheerios_crush. Qed.

Instance byte_Serializer : Serializer byte :=
  {| serialize := Writer.putByte;
     deserialize := Reader.getByte;
     serialize_deserialize_id := byte_serialize_deserialize_id |}.

Lemma byte_unwrap : forall b, Writer.unwrap (serialize b) = [b].
Proof.
  unfold serialize. simpl.
  cheerios_crush.
Qed.

Hint Rewrite byte_unwrap : cheerios.

Definition bool_serialize (b : bool) : Writer.t :=
  if b then serialize x01 else serialize x00.

Definition bool_deserialize :=
  b <- deserialize ;;
    match b with
    | x00 => Reader.ret false
    | x01 => Reader.ret true
    | _ => Reader.error
    end.

Lemma bool_serialize_deserialize_id :
  serialize_deserialize_id_spec bool_serialize bool_deserialize.
Proof.
  intros.
  unfold bool_serialize, bool_deserialize.
  destruct a;
    cheerios_crush; simpl; cheerios_crush.
Qed.

Global Instance bool_Serializer : Serializer bool :=
  {| serialize := bool_serialize;
     deserialize := bool_deserialize;
     serialize_deserialize_id := bool_serialize_deserialize_id |}.

(* this needs to go here because we need the bool_Serializer instance *)
Lemma fold_append_unwrap :
  forall {S A : Type}
         (f : byte -> S -> fold_state S A) (s : S)
         (b : byte) (tail : Writer.t) (bin : list byte),
    Reader.unwrap (Reader.fold f s)
                        (Writer.unwrap (Writer.append
                                              (fun _ => (serialize b))
                                              (fun _ => tail)) ++ bin) =
    match f b s with
    | Done a => Some(a, Writer.unwrap tail ++ bin)
    | More s => Reader.unwrap (Reader.fold f s)
                                    (Writer.unwrap tail ++ bin)
    | Error => None
    end.
Proof.
  cheerios_crush.
Qed.

Lemma fold_append_unwrap' :
  forall {S A : Type}
         (f : byte -> S -> fold_state S A) (s : S)
         (b : byte) (tail : Writer.t) (bin : list byte),
    Reader.unwrap (Reader.fold f s)
                        (Writer.unwrap (Writer.append
                                              (fun _ => (Writer.putByte b))
                                              (fun _ => tail)) ++ bin) =
  match f b s with
    | Done a => Some(a, Writer.unwrap tail ++ bin)
    | More s => Reader.unwrap (Reader.fold f s)
                                    (Writer.unwrap tail ++ bin)
    | Error => None
    end.
Proof.
  cheerios_crush.
Qed.
Hint Rewrite @fold_append_unwrap @fold_append_unwrap' : cheerios.


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

Fixpoint positive_serialize p :=
  match p with
  | xI (xI (xI p)) => Writer.append (fun _ => (serialize x0e))
                                    (fun _ => (positive_serialize p))
  | xI (xI (xO p)) => Writer.append (fun _ => (serialize x0d))
                                    (fun _ => (positive_serialize p))
  | xI (xO (xI p)) => Writer.append (fun _ => (serialize x0c))
                                    (fun _ => (positive_serialize p))
  | xI (xO (xO p)) => Writer.append (fun _ => (serialize x0b))
                                    (fun _ => (positive_serialize p))
  | xO (xI (xI p)) => Writer.append (fun _ => (serialize x0a))
                                    (fun _ => (positive_serialize p))
  | xO (xI (xO p)) => Writer.append (fun _ => (serialize x09))
                                    (fun _ => (positive_serialize p))
  | xO (xO (xI p)) => Writer.append (fun _ => (serialize x08))
                                    (fun _ => (positive_serialize p))
  | xO (xO (xO p)) => Writer.append (fun _ => (serialize x07))
                                    (fun _ => (positive_serialize p))
  | xI (xI p) => Writer.append (fun _ => (serialize x06))
                               (fun _ => (positive_serialize p))
  | xI (xO p) => Writer.append (fun _ => (serialize x05))
                               (fun _ => (positive_serialize p))
  | xO (xI p) => Writer.append (fun _ => (serialize x04))
                               (fun _ => (positive_serialize p))
  | xO (xO p) => Writer.append (fun _ => (serialize x03))
                               (fun _ => (positive_serialize p))
  | xI p => Writer.append (fun _ => (serialize x02))
                          (fun _ => (positive_serialize p))
  | xO p => Writer.append (fun _ => (serialize x01))
                          (fun _ => (positive_serialize p))
  | XH => serialize x00
  end.

Definition depositive_serialize_step
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
    Reader.unwrap (Reader.fold depositive_serialize_step k)
                        (Writer.unwrap (positive_serialize p) ++ bytes)
    = Some(k p, bytes).

Lemma positive_step :
  forall (p : positive), positive_step_aux p.
Proof.
  apply strongind_pos; unfold positive_step_aux.
  - unfold positive_serialize.
    cheerios_crush.
  - split;
      intros;
      try destruct q;
      try destruct q;
      simpl; cheerios_crush; simpl; rewrite H || cheerios_crush;
        try reflexivity;
        repeat constructor.
Qed.

Definition positive_deserialize :=
  Reader.fold depositive_serialize_step (fun p => p).

Theorem positive_serialize_deserialize_id :
  serialize_deserialize_id_spec positive_serialize
                                positive_deserialize.
Proof.
  intros.
  unfold positive_deserialize.
  apply positive_step.
Qed.

Instance positive_Serializer : Serializer positive.
Proof.
  exact ({| serialize := positive_serialize;
            deserialize := positive_deserialize;
            serialize_deserialize_id := positive_serialize_deserialize_id
         |}).
Qed.



(* This is the first example of a "typical" serializer: it combines more
   primitive serializers (in this case, just for byte and positive) together in
   order to serialize a Z. *)
Definition Z_serialize (z : Z) : Writer.t :=
  match z with
  | Z0 => serialize x00
  | Zpos p => Writer.append (fun _ => (serialize x01))
                            (fun _ => (serialize p))
  | Zneg p => Writer.append (fun _ => (serialize x02))
                            (fun _ => (serialize p))
  end.

Definition Z_deserialize : Reader.t Z :=
  tag <- deserialize ;;
  match tag with
  | x02 => Zneg <$> deserialize
  | x01 => Zpos <$> deserialize
  | x00 => Reader.ret Z0
  | _ => Reader.error
  end.

(* This proof is typical for serializing an algebraic datatype. Unfold the
   serializer and deserializer, then do a case analysis and call
   serialize_deserialize_id_crush. *)
Lemma Z_serialize_deserialize_id :
  serialize_deserialize_id_spec Z_serialize Z_deserialize.
Proof.
  intros.
  unfold Z_serialize, Z_deserialize.
  destruct a;
   repeat (cheerios_crush; simpl).
Qed.

Instance Z_Serializer : Serializer Z :=
  {| serialize := Z_serialize;
     deserialize := Z_deserialize;
     serialize_deserialize_id := Z_serialize_deserialize_id
  |}.

Definition N_serialize n :=
  match n with
  | N0 => serialize false
  | Npos p => Writer.append (fun _ => (serialize true))
                            (fun _ => (serialize p))
  end.

Definition N_deserialize : Reader.t N :=
  tag <- deserialize ;;
  match tag with
  | false => Reader.ret N0
  | true => Npos <$> deserialize
  end.

Lemma N_serialize_deserialize_id :
  serialize_deserialize_id_spec N_serialize N_deserialize.
Proof.
  intros.
  unfold N_serialize, N_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance N_Serializer : Serializer N :=
  {| serialize := N_serialize;
     deserialize := N_deserialize;
     serialize_deserialize_id := N_serialize_deserialize_id
  |}.




(* The other main way to define a serializer is to use an isomorphism to another
   type that is already serializable. *)
Definition nat_serialize n : Writer.t := serialize (N.of_nat n).

Definition nat_deserialize : Reader.t nat := N.to_nat <$> deserialize.


(* This proof is typical for serializers defined by converting to and from a
   type that is already serializable. Unfold the serializer and deserializer,
   call serialize_deserialize_id_crush, and then use the proof that the
   conversion functions are inverses. *)
Lemma nat_serialize_deserialize_id :
  serialize_deserialize_id_spec nat_serialize nat_deserialize.
Proof.
  unfold nat_serialize, nat_deserialize.
  cheerios_crush.
  now rewrite Nnat.Nat2N.id.
Qed.

Instance nat_Serializer : Serializer nat.
Proof.
  exact {| serialize := nat_serialize;
           deserialize := nat_deserialize;
           serialize_deserialize_id := nat_serialize_deserialize_id
        |}.
Qed.

(* Serializer for the standard library's Fin.t based on converting to nat. *)
Definition Fin_serialize {n} (x : Fin.t n) : Writer.t :=
  serialize (proj1_sig (Fin.to_nat x)).

Definition Fin_deserialize {n} : Reader.t (Fin.t n) :=
  m <- deserialize ;;
    match Fin.of_nat m n with
    | inleft x => Reader.ret x
    | inright _ => Reader.error
    end.

Lemma Fin_of_nat_to_nat:
  forall (n : nat) (a : Fin.t n), Fin.of_nat (proj1_sig (Fin.to_nat a)) n = inleft a.
Proof.
  induction a.
  - auto.
  - simpl. break_let. simpl in *.
    now rewrite IHa.
Qed.

Lemma Fin_serialize_deserialize_id n : serialize_deserialize_id_spec Fin_serialize (@Fin_deserialize n).
Proof.
  unfold Fin_serialize, Fin_deserialize.
  cheerios_crush.
  rewrite Fin_of_nat_to_nat.
  cheerios_crush.
Qed.

Instance Fin_Serializer n : Serializer (Fin.t n) :=
  {| serialize := Fin_serialize;
     deserialize := Fin_deserialize;
     serialize_deserialize_id := Fin_serialize_deserialize_id n
  |}.

(* Serializer for StructTact's fin based on converting to nat. *)
Definition fin_serialize {n} (x : fin n) : Writer.t :=
  serialize (fin_to_nat x).

Definition fin_deserialize {n} : Reader.t (fin n) :=
  m <- deserialize ;;
    match fin_of_nat m n with
    | inleft x => Reader.ret x
    | inright _ => Reader.error
    end.

Lemma fin_serialize_deserialize_id n : serialize_deserialize_id_spec fin_serialize (@fin_deserialize n).
Proof.
  unfold fin_serialize, fin_deserialize.
  cheerios_crush.
  rewrite fin_of_nat_fin_to_nat.
  cheerios_crush.
Qed.

Instance fin_Serializer n : Serializer (fin n) :=
  {| serialize := fin_serialize;
     deserialize := fin_deserialize;
     serialize_deserialize_id := fin_serialize_deserialize_id n
  |}.

Definition ascii_serialize (a : Ascii.ascii) : Writer.t :=
  serialize (Ascii.nat_of_ascii a).

Definition ascii_deserialize : Reader.t Ascii.ascii :=
  Ascii.ascii_of_nat <$> deserialize.

Lemma ascii_serialize_deserialize_id :
  serialize_deserialize_id_spec ascii_serialize ascii_deserialize.
Proof.
  unfold ascii_deserialize, ascii_serialize.
  cheerios_crush.
  now rewrite Ascii.ascii_nat_embedding.
Qed.

Instance ascii_Serializer : Serializer Ascii.ascii :=
  {| serialize := ascii_serialize;
     deserialize := ascii_deserialize;
     serialize_deserialize_id := ascii_serialize_deserialize_id
  |}.
End BasicSerializers.
