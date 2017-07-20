Require Import Ascii List ZArith.
Import ListNotations.

Require Import Cheerios.Types.

Set Implicit Arguments.

Module IOStreamWriter : WRITER.
  Inductive iostream :=
  | Empty : iostream
  | WriteByte : byte -> iostream
  | Seq : iostream -> (unit -> iostream) -> iostream.

  Definition t := iostream.

  Fixpoint iostreamDenote (i : iostream) : list byte :=
    match i with
    | Empty => []
    | WriteByte b => [b]
    | Seq i1 i2 => iostreamDenote i1 ++ iostreamDenote (i2 tt)
    end.

  Definition unwrap := iostreamDenote.

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
  Proof. reflexivity. Qed.

  Lemma putByte_unwrap : forall (a : byte), unwrap (putByte a) = [a].
  Proof. reflexivity. Qed.

  Definition wire := list byte.

  Axiom wire_eq_dec : forall w w' : wire, {w = w'} + {w <> w'}.

  Definition wire_wrap := unwrap.

  Definition wire_unwrap (x : wire) := x.

  Lemma wire_wrap_unwrap : forall x, wire_unwrap (wire_wrap x) = unwrap x.
  Proof. reflexivity. Qed.
End IOStreamWriter.

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

  Fixpoint fold {S A}
           (f : byte -> S -> fold_state S A) (s : S) (l : list byte) :=
    match l with
    | [] => None
    | b :: l => match f b s with
                | Done a => Some (a, l)
                | More s => fold f s l
                | Error => None
                end
    end.

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
    simpl. destruct l; reflexivity.
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

(* In panrticular, if there is nothing else in the bitsream, then deserialize and
   serialize are inverses. *)
Lemma serialize_deserialize_id_nil :
  forall A (sA : Serializer A) a,
    ByteListReader.unwrap deserialize (IOStreamWriter.unwrap (serialize a)) = Some (a, []).
Proof.
  intros.
  pose proof serialize_deserialize_id a [].
  now rewrite app_nil_r in *.
Qed.

Definition serialize_top {A: Type} {sA: Serializer A}
           (s : A -> IOStreamWriter.t) (a : A) : IOStreamWriter.wire :=
  IOStreamWriter.wire_wrap (s a).

Definition deserialize_top {A: Type} {sA: Serializer A}
           (d : ByteListReader.t A) (w : IOStreamWriter.wire) : option A :=
  match ByteListReader.unwrap d (IOStreamWriter.wire_unwrap w) with
  | None => None
  | Some (a, _) => Some a
  end.

Theorem serialize_deserialize_top_id : forall {A : Type} {sA: Serializer A} a,
    deserialize_top deserialize (serialize_top serialize a) = Some a.
Proof.
  intros.
  unfold serialize_top, deserialize_top.
  rewrite IOStreamWriter.wire_wrap_unwrap.
  now rewrite serialize_deserialize_id_nil.
Qed.
