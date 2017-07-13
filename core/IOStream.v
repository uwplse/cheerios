Require Import Cheerios.Core.
Require Import Cheerios.Types.

Require Import List.
Import ListNotations.

Module IOStream : WRITER.
  Inductive iostream :=
  | Done : iostream
  | WriteByte : byte -> (unit -> iostream) -> iostream
  | Seq : iostream -> iostream -> iostream.

  Definition t := iostream.

  Fixpoint iostreamDenote (i : iostream) : list byte :=
    match i with
    | Done => []
    | WriteByte b thunk => b :: iostreamDenote (thunk tt)
    | Seq i1 i2 => iostreamDenote i1 ++ iostreamDenote i2
    end.

  Definition unwrap := iostreamDenote.

  (* serializers *)
  Definition empty : iostream := Done.

  Definition putByte : byte -> iostream :=
    fun b => WriteByte b (fun _ => Done).

  Fixpoint putList (l : list byte) :  iostream :=
    match l with
    | [] => Done
    | b :: l => WriteByte b (fun _ => putList l)
    end.

  Definition append : iostream -> iostream -> iostream := Seq.

  Lemma empty_unwrap : unwrap empty = [].
  Proof. reflexivity. Qed.
    
  Lemma append_unwrap :
    forall x y : t, unwrap (append x y) = unwrap x ++ unwrap y.
  Proof. reflexivity. Qed.
  
  Lemma putByte_unwrap : forall (a : byte), unwrap (putByte a) = [a].
  Proof. reflexivity. Qed.

  Definition wire := list byte.

  Axiom wire_eq_dec : forall w w' : wire, {w = w'} + {w <> w'}.

  Definition wire_wrap := unwrap.

  Definition wire_unwrap (x : wire) := x.

  Lemma wire_wrap_unwrap : forall x, wire_unwrap (wire_wrap x) = unwrap x.
  Proof. reflexivity. Qed.
End IOStream.

Module IOStreamSerializer := SerializerClass IOStream Deserializer.