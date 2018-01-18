Require Import Ascii List ZArith.
Import ListNotations.

Require Import Cheerios.Types.
Require Import Cheerios.ByteDecidable.

Set Implicit Arguments.

Module IOStreamWriter : WRITER.
  Inductive iostream :=
  | Empty : iostream
  | WriteByte : byte -> iostream
  | Seq : iostream -> (unit -> iostream) -> iostream.

  Definition t := iostream.

  Fixpoint iostreamDenote (i : iostream) : list byte * nat :=
    match i with
    | Empty => ([], 0)
    | WriteByte b => ([b], 1)
    | Seq i1 i2 => match iostreamDenote i1, iostreamDenote (i2 tt) with
                   | (l1, n1), (l2, n2) => (l1 ++ l2, n1 + n2)
                   end
    end.

  Definition unwrap i := fst (iostreamDenote i).

  (* serializers *)
  Definition empty : iostream := Empty.

  Definition putByte : byte -> iostream :=
    WriteByte.

  Definition append : (unit -> iostream) -> (unit -> iostream) -> iostream :=
    fun t1 t2 => Seq (t1 tt) t2.

  Lemma empty_unwrap : unwrap empty = [].
  Proof. reflexivity. Qed.

  Lemma append_unwrap :
    forall x y : unit -> t, unwrap (append x y) = unwrap (x tt) ++ unwrap (y tt).
  Proof.
    intros.
    unfold unwrap.
    simpl.
    destruct (iostreamDenote (x tt)).
    destruct (iostreamDenote (y tt)).
    reflexivity.
  Qed.

  Lemma putByte_unwrap : forall (a : byte), unwrap (putByte a) = [a].
  Proof. reflexivity. Qed.

  (* wire *)
  Definition wire := list byte.

  Definition wire_eq_dec := list_eq_dec byte_eq_dec.

  Definition wire_wrap := unwrap.

  Definition wire_unwrap (x : wire) := x.

  Lemma wire_wrap_unwrap : forall x, wire_unwrap (wire_wrap x) = unwrap x.
  Proof. reflexivity. Qed.

  (* channel *)
  Definition out_channel := list byte.
  Definition in_channel := list byte.

  Definition out_channel_wrap s := unwrap s.
  Definition channel_send (o : out_channel) : in_channel := o.
  Definition in_channel_unwrap (i : in_channel) : list byte := i.

  Theorem channel_wrap_unwrap : forall x,
      in_channel_unwrap (channel_send (out_channel_wrap x)) = unwrap x.
  Proof.
    reflexivity.
  Qed.
End IOStreamWriter.

Notation "a +$+ b" := (IOStreamWriter.append (fun _ => a) (fun _ => b))
                      (at level 60, right associativity).

(* This is the monad used to write deserializers. It is a state monad with
    failure, where the state is the serialized bits. *)

Module ByteListReader : READER.
  Definition t (A : Type) := list byte -> option (A * list byte).
  Definition unwrap {A} (x : t A) := x.

  Definition getByte (l : list byte) :=
    match l with
    | [] => None
    | b :: l => Some (b, l)
    end.

  Definition ret {A} (a : A) : t A := fun s => Some (a, s).

  Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
    fun s => match m s with None => None
                       | Some (a, s') => f a s'
             end.

  Definition map {A B} (f : A -> B) (d : t A) : t B :=
    bind d (fun a => ret (f a)).

  Definition error {A} : t A :=
    fun l => None.

  Lemma getByte_unwrap : forall l,
      unwrap getByte l = match l with
                         | [] => None
                         | b :: l => Some (b, l)
                         end.
  Proof. reflexivity. Qed.

  Lemma bind_unwrap : forall A B (m : t A)
                             (f : A -> t B) bytes,
      unwrap (bind m f) bytes = match unwrap m bytes with
                                | None => None
                                | Some (v, bytes) => unwrap (f v) bytes
                                end.
  Proof.
    unfold bind.
    intros.
    reflexivity.
  Qed.

  (* state machines *)

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

  Definition fold {S A} (f : state_machine S A) (s : S) (l : list byte) :=
    match run f s l with
    | Done (a, l) => Some (a, l)
    | _ => None
    end.

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
      destruct (f a s); try reflexivity.
      rewrite IHl1.
      reflexivity.
  Qed.

  Definition one : state_machine unit byte :=
    fun b _ => Done b.

  Lemma fold_one : forall (bytes : list byte),
      unwrap (fold one tt) bytes = match bytes with
                                   | [] => None
                                   | b :: l => Some (b, l)
                                   end.
  Proof.
    destruct bytes;
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
    unfold unwrap.
    intros until bytes.
    induction bytes.
    - reflexivity.
    - intros s.
      unfold run.
      simpl.
      destruct (b _ _);
        auto.
  Qed.

  Lemma fold_pair_inr : forall S1 A S2 B
                               (a : state_machine S1 A) (b : state_machine S2 B)
                               x bytes s,
      unwrap (fold (pair a b) (inr (x, s))) bytes =
      match unwrap (fold b s) bytes with
      | Some (y, l) => Some ((x, y), l)
      | None => None
      end.
  Proof.
    intros.
    unfold unwrap, fold.
    rewrite run_pair_inr.
    destruct (run _ _ _);
      auto.
    destruct a0.
    reflexivity.
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
    unfold unwrap.
    intros until bytes.
    induction bytes.
    - reflexivity.
    - intros.
      simpl.
      destruct a; auto.
  Qed.

  Lemma fold_pair_inl : forall S1 A S2 B
                               (a : state_machine S1 A) (b : state_machine S2 B)
                               bytes s1 s2,
      unwrap (fold (pair a b) (inl (s1, s2))) bytes =
      match unwrap (fold a s1) bytes with
      | Some (x, l) => unwrap (fold (pair a b) (inr (x, s2))) l
      | None => None
      end.
  Proof.
    intros.
    unfold unwrap, fold.
    rewrite run_pair_inl.
    destruct (run _ _ _); auto.
    destruct a0.
    reflexivity.
  Qed.

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
    unfold unwrap.
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
    unfold unwrap.
    induction bytes; simpl; intros.
    - reflexivity.
    - destruct b; auto.
  Qed.

  Definition choice {S1 A S2 B} (a : state_machine S1 A) (b : state_machine S2 B) : state_machine (S1 + S2) (A + B) :=
    fun byte s =>
      match s with
      | inl s =>
        match a byte s with
        | Done a => Done (inl a)
        | More s => More (inl s)
        | Error => Error
        end
      | inr s =>
        match b byte s with
        | Done b => Done (inr b)
        | More s => More (inr s)
        | Error => Error
        end
      end.

  Definition bind_sm {S1 A S2 B} (a : state_machine S1 A) (b : A -> state_machine S2 B) :
    state_machine (S1 * S2 + A * S2) B :=
    fun byte s =>
      match s with
      | inl (s1, s2) =>
        match a byte s1 with
        | Done x => More (inr (x, s2))
        | More s1 => More (inl (s1, s2))
        | Error => Error
        end
      | inr (x, s2) =>
        match b x byte s2 with
        | Done y => Done y
        | More s2 => More (inr (x, s2))
        | Error => Error
        end
      end.

  (* lemmas not about state machines *)

  Lemma ret_unwrap : forall {A} (x: A) bytes, unwrap (ret x) bytes = Some (x, bytes).
  Proof. reflexivity. Qed.

  Lemma map_unwrap: forall A B (f: A -> B) (d: t A) bytes,
      unwrap (map f d) bytes =
      match (unwrap d bytes) with
      | None => None
      | Some (v, bytes) => Some (f v, bytes)
      end.
  Proof. reflexivity. Qed.

  Lemma fold_unwrap : forall {S A : Type}
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
  Proof.
    intros.
    unfold fold.
    destruct l.
    - unfold unwrap.
      simpl.
      reflexivity.
    - unfold unwrap.
      simpl.
      now destruct (f b s).
  Qed.


End ByteListReader.
Arguments ByteListReader.error {_}.

Notation serialize_deserialize_id_spec s d :=
  (forall a bytes,
      ByteListReader.unwrap d (IOStreamWriter.unwrap (s a) ++ bytes) = Some(a, bytes)).

(* This is the class of serializable types, which is the main entrypoint to
   Cheerios. Instances are required to show that `deserialize` can correctly
   recognize a piece of `serialize`d data at the prefix of an arbitrary
   bitstream. *)
Class Serializer (A : Type) : Type :=
  {
    serialize : A -> IOStreamWriter.t;
    deserialize : ByteListReader.t A;
    serialize_deserialize_id : serialize_deserialize_id_spec serialize deserialize
  }.
Hint Rewrite @serialize_deserialize_id : cheerios.

(* In particular, if there is nothing else in the bitsream, then deserialize and
   serialize are inverses. *)
Lemma serialize_deserialize_id_nil :
  forall A (sA : Serializer A) a,
    ByteListReader.unwrap deserialize (IOStreamWriter.unwrap (serialize a)) = Some (a, []).
Proof.
  intros.
  pose proof serialize_deserialize_id a [].
  now rewrite app_nil_r in *.
Qed.

(* top-level interface for wire type *)

Definition serialize_top (s : IOStreamWriter.t) : IOStreamWriter.wire :=
  IOStreamWriter.wire_wrap s.

Definition deserialize_top {A: Type}
           (d : ByteListReader.t A) (w : IOStreamWriter.wire) : option A :=
  match ByteListReader.unwrap d (IOStreamWriter.wire_unwrap w) with
  | Some (a, []) => Some a
  | _ => None
  end.

Lemma serialize_deserialize_top_id' : forall {A} (d : ByteListReader.t A) s v,
    ByteListReader.unwrap d (IOStreamWriter.unwrap s) = Some (v, []) ->
    deserialize_top d (serialize_top s) = Some v.
Proof.
  intros.
  unfold serialize_top, deserialize_top.
  rewrite IOStreamWriter.wire_wrap_unwrap, H.
  reflexivity.
Qed.

Lemma serialize_deserialize_top_invert : forall {A} (d : ByteListReader.t A) s v,
    deserialize_top d (serialize_top s) = Some v ->
    ByteListReader.unwrap d (IOStreamWriter.unwrap s) = Some (v, []).

Proof.
  intros.
  unfold serialize_top, deserialize_top.
  rewrite <-IOStreamWriter.wire_wrap_unwrap.
  unfold deserialize_top, serialize_top in H.
  destruct (ByteListReader.unwrap d (IOStreamWriter.wire_unwrap (IOStreamWriter.wire_wrap s))).
  - destruct p.
    destruct l;
      inversion H.
    reflexivity.
  - inversion H.
Qed.

Theorem serialize_deserialize_top_id : forall {A : Type} {sA: Serializer A} a,
    deserialize_top deserialize (serialize_top (serialize a)) = Some a.
Proof.
  intros.
  apply serialize_deserialize_top_id'.
  apply serialize_deserialize_id_nil.
Qed.

Axiom wire_serialize : IOStreamWriter.wire -> IOStreamWriter.t.
Axiom wire_deserialize : ByteListReader.t IOStreamWriter.wire.
Axiom wire_serialize_deserialize_id :
  serialize_deserialize_id_spec wire_serialize wire_deserialize.

Instance wire_Serializer : Serializer IOStreamWriter.wire.
Proof.
  exact {| serialize := wire_serialize;
           deserialize := wire_deserialize;
           serialize_deserialize_id := wire_serialize_deserialize_id |}.
Qed.

(* top-level interface for output and input channels *)

Definition to_channel : IOStreamWriter.t -> IOStreamWriter.out_channel :=
  IOStreamWriter.out_channel_wrap.

Definition from_channel {A} (d : ByteListReader.t A) (i : IOStreamWriter.in_channel) :=
  match ByteListReader.unwrap d (IOStreamWriter.in_channel_unwrap i) with
  | Some (a, []) => Some a
  | _ => None
  end.

Theorem serialize_deserialize_channel_id : forall {A} {sA : Serializer A} a,
    from_channel deserialize (IOStreamWriter.channel_send (to_channel (serialize a))) = Some a.
Proof.
  intros.
  unfold to_channel, from_channel.
  rewrite IOStreamWriter.channel_wrap_unwrap.
  rewrite serialize_deserialize_id_nil.
  reflexivity.
Qed.