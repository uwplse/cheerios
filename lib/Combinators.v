Require Import StructTactics.
Require Import List.
Require Import Types.

SearchAbout Serializer.

Eval cbv in serialize Bool_Serializer true.

Definition pair_serialize
           (A B: Type)
           (aSerializer: Serializer A)
           (bSerializer: Serializer B)
           (p: A*B) :=
  let (a, b) := p in
  (serialize A) aSerializer ++ (serialize bSerializer b).

Definition pair_deserialize
         {A:Type}
         {serialize_a: A -> list bool}
         {deserialize_a: list bool -> option (A * list bool)}
         {SA: Serializer serialize_a deserialize_a}
         {B:Type}
         {serialize_b: B -> list bool}
         {deserialize_b: list bool -> option (B * list bool)}
         {SB: Serializer serialize_b deserialize_b}
         (bin : list bool) : option ((A*B) * list bool) :=
  match deserialize_a bin with
    | None => None
    | Some (a, rest) =>
  match deserialize_b rest with
    | None => None
    | Some (b, remainder) =>
      Some ((a, b), remainder)
  end
  end.

Instance Pair_Serializer: Serializer pair_serialize pair_deserialize.
split; intros.
- destruct x.
  unfold pair_serialize. unfold pair_deserialize. simpl.
  reflexivity.
- unfold pair_deserialize in H.
  repeat break_match; inversion H.
  + subst.
    unfold pair_serialize.
    unfold bool_serialize. simpl.
    unfold bool_deserialize in Heqo0.
    break_match; inversion Heqo0.
    subst.
    unfold bool_deserialize in Heqo.
    break_match; inversion Heqo.
    subst.
    reflexivity.
Qed.

Compute pair_serialize (true, false).