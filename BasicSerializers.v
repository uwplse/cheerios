Require Import ZArith.

From StructTact Require Import StructTactics Fin.
Require Fin Ascii.

From Cheerios Require Import Monoid Core Tactics DeserializerMonad.
Import DeserializerNotations.

Section bin.
  Variable bin : Type.
  Context {mbin : Monoid bin}.
  Context {sbool : Serializer bin bool}.
  Context {spos : Serializer bin positive}.

(* This is the first example of a "typical" serializer: it combines more
   primitive serializers (in this case, just for bool and positive) together in
   order to serialize a Z. *)
Definition Z_serialize (z : Z) : bin :=
  match z with
  | Z0 => serialize false
  | Zpos p => serialize true +++ serialize true +++ serialize p
  | Zneg p => serialize true +++ serialize false +++ serialize p
  end.

Definition Z_deserialize : deserializer bin Z :=
  tag <- deserialize ;;
  match tag with
  | true => sign <- deserialize ;;
           (match sign with true => Zpos | false => Zneg end) <$> deserialize
  | false => ret Z0
  end.

(* This proof is typical for serializing an algebraic datatype. Unfold the
   serializer and deserializer, then do a case analysis and call
   cheerios_crush. *)
Lemma Z_serialize_deserialize_id :
  serialize_deserialize_id_spec Z_serialize Z_deserialize.
Proof.
  unfold Z_serialize, Z_deserialize.
  destruct a; cheerios_crush.
Qed.

Global Instance Z_Serializer : Serializer bin Z :=
  {| serialize := Z_serialize;
     deserialize := Z_deserialize;
     serialize_deserialize_id := Z_serialize_deserialize_id
  |}.


Definition N_serialize (n : N) : bin :=
  match n with
  | N0 => serialize false
  | Npos p => serialize true +++ serialize p
  end.

Definition N_deserialize : deserializer bin N :=
  tag <- deserialize ;;
  match tag with
  | false => ret N0
  | true => Npos <$> deserialize
  end.

Lemma N_serialize_deserialize_id :
  serialize_deserialize_id_spec N_serialize N_deserialize.
Proof.
  unfold N_serialize, N_deserialize.
  destruct a; cheerios_crush.
Qed.

Global Instance N_Serializer : Serializer bin N :=
  {| serialize := N_serialize;
     deserialize := N_deserialize;
     serialize_deserialize_id := N_serialize_deserialize_id
  |}.


(* The other main way to define a serializer is to use an isomorphism to another
   type that is already serializable. *)
Definition nat_serialize (n : nat) : bin := serialize (N.of_nat n).

Definition nat_deserialize : deserializer bin nat := N.to_nat <$> deserialize.

(* This proof is typical for serializers defined by converting to and from a
   type that is already serializable. Unfold the serializer and deserializer,
   call cheerios_crush, and then use the proof that the
   conversion functions are inverses. *)
Lemma nat_serialize_deserialize_id :
  serialize_deserialize_id_spec nat_serialize nat_deserialize.
Proof.
  unfold nat_serialize, nat_deserialize.
  cheerios_crush.
  now rewrite Nnat.Nat2N.id.
Qed.

Global Instance nat_Serializer : Serializer bin nat :=
  {| serialize := nat_serialize;
     deserialize := nat_deserialize;
     serialize_deserialize_id := nat_serialize_deserialize_id
  |}.


(* Serializer for the standard library's Fin.t based on converting to nat. *)
Definition Fin_serialize {n} (x : Fin.t n) : bin :=
  serialize (proj1_sig (Fin.to_nat x)).

Definition Fin_deserialize {n} : deserializer bin (Fin.t n) :=
  m <- deserialize ;;
    match Fin.of_nat m n with
    | inleft x => ret x
    | inright _ => fail
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
  now rewrite Fin_of_nat_to_nat.
Qed.

Global Instance Fin_Serializer n : Serializer bin (Fin.t n) :=
  {| serialize := Fin_serialize;
     deserialize := Fin_deserialize;
     serialize_deserialize_id := Fin_serialize_deserialize_id n
  |}.


(* Serializer for StructTact's fin based on converting to nat. *)
Definition fin_serialize {n} (x : fin n) : bin :=
  serialize (fin_to_nat x).

Definition fin_deserialize {n} : deserializer bin (fin n) :=
  m <- deserialize ;;
    match fin_of_nat m n with
    | inleft x => ret x
    | inright _ => fail
    end.

Lemma fin_serialize_deserialize_id n : serialize_deserialize_id_spec fin_serialize (@fin_deserialize n).
Proof.
  unfold fin_serialize, fin_deserialize.
  cheerios_crush.
  now rewrite fin_of_nat_fin_to_nat.
Qed.

Global Instance fin_Serializer n : Serializer bin (fin n) :=
  {| serialize := fin_serialize;
     deserialize := fin_deserialize;
     serialize_deserialize_id := fin_serialize_deserialize_id n
  |}.


Definition ascii_serialize (a : Ascii.ascii) : bin :=
  serialize (Ascii.nat_of_ascii a).

Definition ascii_deserialize : deserializer bin Ascii.ascii :=
  Ascii.ascii_of_nat <$> deserialize.

Lemma ascii_serialize_deserialize_id :
  serialize_deserialize_id_spec ascii_serialize ascii_deserialize.
Proof.
  unfold ascii_deserialize, ascii_serialize.
  cheerios_crush.
  now rewrite Ascii.ascii_nat_embedding.
Qed.

Global Instance ascii_Serializer : Serializer bin Ascii.ascii :=
  {| serialize := ascii_serialize;
     deserialize := ascii_deserialize;
     serialize_deserialize_id := ascii_serialize_deserialize_id
  |}.
End bin.