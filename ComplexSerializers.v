Require Import Ascii.
Require Import String.
Require Import List.
Require Import Cheerios.Types.
Require Import Cheerios.Combinators.

Fixpoint string_to_list s :=
  match s with
    | EmptyString => nil
    | String c s' => c :: (string_to_list s')
  end.

Fixpoint list_to_string l :=
  match l with
    | nil => EmptyString
    | h::l' => String h (list_to_string l')
  end.

Lemma string_to_list_to_string : forall s,
                                  list_to_string (string_to_list s) = s.
Proof.
  induction s; auto; simpl.
  now rewrite IHs.
Qed.

Definition string_serialize (s : string) :=
  serialize (string_to_list s).

Definition string_deserialize bin : option (string * list bool) :=
  match deserialize bin with
    | None => None
    | Some (cs, rest) => Some (list_to_string cs, rest)
  end.

Lemma string_serialize_reversible : forall s bin,
    string_deserialize (string_serialize s ++ bin) = Some (s, bin).
Proof.
  unfold string_deserialize, string_serialize.
  intros s bin.
  rewrite Serialize_reversible.
  now rewrite string_to_list_to_string.
Qed.

Instance string_Serializer : Serializer string :=
  {|
    serialize := string_serialize;
    deserialize := string_deserialize;
    Serialize_reversible := string_serialize_reversible
  |}.