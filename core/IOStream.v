Require Import Cheerios.Types.

Require Import List.
Import ListNotations.

Module IOStream : WRITER.
  Inductive iostream :=
  | Done : iostream
  | WriteByte : byte -> iostream
  | Seq : iostream -> (unit -> iostream) -> iostream.

  Definition t := iostream.

  Fixpoint iostreamDenote (i : iostream) : list byte :=
    match i with
    | Done => []
    | WriteByte b => [b]
    | Seq i1 i2 => iostreamDenote i1 ++ iostreamDenote (i2 tt)
    end.

  Definition unwrap := iostreamDenote.

  (* serializers *)
  Definition empty : iostream := Done.

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
End IOStream.
