Require Import Cheerios.BasicSerializers.
Require Import Cheerios.Core.
Require Import Cheerios.DeserializerMonad.
Require Import Cheerios.Types.

(*
   Most user-defined datatypes are tree-like, which are typically nontrivial to
   deserialize by structural recursion on the bitstream. This file provides a
   generic multi-arity tree type and its serializer/deserializer. Other tree-like
   types can be serialized by first converting to a tree and then serializing.
*)

Require Import List.
Import ListNotations.

Require Import Cheerios.Cheerios.
Import DeserializerNotations.

Set Implicit Arguments.

Section tree.
  (* The tree is parametrized on the type of data stored at the leaves. *)
  Variable A : Type.

  (* Each node of the tree contains a list of subtrees.
     Coq does not generate a useful induction scheme for such types,
     so we just tell it not to generate anything, and we'll write our own. *)
  Local Unset Elimination Schemes.

  Inductive tree : Type :=
  | atom : A -> tree
  | node : list tree -> tree
  .

  (* Here is an actually useful recursion principle for tree,
     which requires an additional motive P_list. *)
  Section tree_rect.
    Variable P : tree -> Type.
    Variable P_list : list tree -> Type.
    Hypothesis P_nil : P_list [].
    Hypothesis P_cons : forall t l, P t -> P_list l -> P_list (t :: l).
    Hypothesis P_atom : forall a, P (atom a).
    Hypothesis P_node : forall l, P_list l -> P (node l).

    Fixpoint tree_rect (t : tree) : P t :=
      let fix go_list (l : list tree) : P_list l :=
          match l with
          | [] => P_nil
          | t :: l => P_cons (tree_rect t) (go_list l)
          end
      in
      match t with
      | atom a => P_atom a
      | node l => P_node (go_list l)
      end.
  End tree_rect.

  (* Setting P_list := List.Forall P is a reasonable default. *)
  Section tree_ind.
    Variable P : tree -> Prop.

    Hypothesis P_atom : forall a, P (atom a).
    Hypothesis P_node : forall l, List.Forall P l -> P (node l).

    Definition tree_ind (t : tree) : P t :=
      tree_rect P (List.Forall P)
                (List.Forall_nil _)
                (fun t l Pt Pl => List.Forall_cons _ Pt Pl) P_atom P_node t.
  End tree_ind.
End tree.

(* The shape of a tree can be expressed by mapping (fun _ => tt) over it. *)
Fixpoint map {A B} (f : A -> B) (t : tree A) : tree B :=
  match t with
  | atom a => atom (f a)
  | node l => node (List.map (map f) l)
  end.

(* Fill out a tree using a list of elements given in preorder traversal order. *)
Fixpoint fill' {A B} (x : tree A) (bs : list B) : option (tree B * list B) :=
  let fix fill'_list (l : list (tree A)) (bs : list B) : option (list (tree B) * list B) :=
      match l with
      | [] => Some ([], bs)
      | x :: l => match fill' x bs with None => None
                 | Some (x, bs) =>
                 match fill'_list l bs with None => None
                 | Some (l, bs) =>
                 Some (x :: l, bs)
                 end
                 end
      end in
  match x with
  | atom _ => match bs with
             | [] => None
             | b :: bs => Some (atom b, bs)
             end
  | node l => match fill'_list l bs with None => None
             | Some (l, bs) => Some (node l, bs)
             end

  end.

(* Copy paste of local definition above. *)
Definition fill'_list {A B} :=
  fix fill'_list (l : list (tree A)) (bs : list B) : option (list (tree B) * list B) :=
      match l with
      | [] => Some ([], bs)
      | x :: l => match fill' x bs with None => None
                 | Some (x, bs) =>
                 match fill'_list l bs with None => None
                 | Some (l, bs) =>
                 Some (x :: l, bs)
                 end
                 end
      end.

Definition fill {A B} (x : tree A) (bs : list B) : option (tree B) :=
  match fill' x bs with None => None
  | Some (t, _) => Some t
  end.

(* Produce a preorder traversal list of elements *)
Fixpoint preorder {A} (x : tree A) : list A :=
  let fix preorder_list (l : list (tree A)) : list A :=
      match l with
      | [] => []
      | x :: l => preorder x ++ preorder_list l
      end
  in
  match x with
  | atom a => [a]
  | node l => preorder_list l
  end.

Definition preorder_list {A} :=
  fix preorder_list (l : list (tree A)) : list A :=
      match l with
      | [] => []
      | x :: l => preorder x ++ preorder_list l
      end.

(* Since the shape is expressed as mapping, we will need the fact that filling
   out the a mapped tree with the elements of the original tree gives the
   original.
 *)
Lemma fill'_preorder :
  forall A B (f : B -> A) t (bs : list B),
    fill' (map f t) (preorder t ++ bs) = Some (t, bs).
Proof.
  intros A B f.
  induction t using tree_rect
  with (P_list := fun l =>
     forall bs,
       fill'_list (List.map (map f) l) (preorder_list l ++ bs) = Some (l, bs)); intros.
  - auto.
  - simpl.
    rewrite app_ass. rewrite  IHt. rewrite IHt0. auto.
  - auto.
  - simpl.
    fold (@preorder_list B).
    fold (@fill'_list A B).
    now rewrite IHt.
Qed.

Lemma fill_preorder :
  forall A B (f : A -> B) t,
    fill (map f t) (preorder t) = Some t.
Proof.
  unfold fill.
  intros.
  rewrite <- app_nil_r with (l := preorder t).
  now rewrite fill'_preorder.
Qed.

Section serializer.
  Variables A : Type.
  Variable sA : Serializer A.

  (* Now we're ready to serialize trees. First, we serialize their shape. *)

  Fixpoint serialize_tree_shape (t : tree A) : Serializer.t :=
    let fix serialize_list_tree_shape (l : list (tree A)) : Serializer.t :=
        match l with
        | [] => Serializer.empty
        | x :: xs => Serializer.append (serialize_tree_shape x)
                                       (serialize_list_tree_shape xs)
        end
    in
    match t with
    | atom _ => serialize x00 (* ignore the data, since we're just focused on the shape *)
    | node l => Serializer.append (serialize x01)
                                  (Serializer.append (serialize_list_tree_shape l)
                                                     (serialize x02))
    end.
  
  Definition serialize_list_tree_shape :=
    fix serialize_list_tree_shape (l : list (tree A)) : Serializer.t :=
        match l with
        | [] => Serializer.empty
        | x :: xs => Serializer.append (serialize_tree_shape x)
                                       (serialize_list_tree_shape xs)
        end.

  Definition deserialize_tree_shape_step (b : byte) (s : list (list (tree unit))) :
    fold_state (list (list (tree unit))) (tree unit) :=
    match b with
    | x00 => match s with
             | [] => Done (atom tt)
             | ts :: s => More ((atom tt :: ts) :: s)
             end
    | x01 => More ([] :: s)
    | x02 => match s with
             | [] => Error
             | ts :: s => let t := node (List.rev ts) in
                          match s with
                          | [] => Done t
                          | ts :: acc => More ((t :: ts) :: acc)
                          end
             end

    | _ => Error
    end.

  Lemma serialize_deserialize_shape_id :
    forall t acc bytes,
      Deserializer.unwrap (Deserializer.fold deserialize_tree_shape_step acc)
                          (Serializer.unwrap (serialize_tree_shape t) ++ bytes) =
      match acc with
      | [] => Some (map (fun _ => tt) t, bytes)
      | j :: js => Deserializer.unwrap
                     (Deserializer.fold deserialize_tree_shape_step
                                        ((map (fun _ => tt) t :: j) :: js)) bytes
      end.
  Proof.
    induction t using tree_rect with
        (P_list := fun l =>
       (* We need to extend the statement to a list of subtrees for the mutual induction
          hypothesis.
          It says that serializing and then deserializing a list of trees `l` is the same
          as `List.map (map (fun _ => tt) l)`.
          `deserialize_list_tree_shape'` is always called with at least one element on the
          accumulator, so there's no need for a match like there was above.
        *)
       forall ts acc bin,
         Deserializer.unwrap
           (Deserializer.fold deserialize_tree_shape_step (ts :: acc))
           (Serializer.unwrap (serialize_list_tree_shape l) ++ bin) =
         Deserializer.unwrap
           (Deserializer.fold
              deserialize_tree_shape_step
              ((List.rev (List.map (map (fun _ => tt)) l) ++ ts) :: acc)) bin);
      intros.
    - cheerios_crush. simpl. cheerios_crush.
    - unfold serialize_list_tree_shape.
      rewrite Serializer.append_unwrap, app_ass, IHt, IHt0.
      simpl.
      now rewrite app_ass.
    - intros.
      repeat (cheerios_crush; simpl).
      now destruct acc.
    - intros.
      simpl.
      rewrite fold_append_unwrap.
      simpl.
      fold serialize_list_tree_shape.
      rewrite Serializer.append_unwrap, app_ass.
      rewrite IHt.
      cheerios_crush. simpl.
      destruct acc;
        rewrite app_nil_r, rev_involutive;
        auto.
  Qed.

      
      
          
          

        
        
        
        



        cheerios_crush. 
        
        fold serialize_list_tree_shape.
        cheerios_crush. unfold serialize_list_tree_shape.
        
          
      fold deserialize_tree_shape_step.

      cheerios_crush.

      
      



  Fixpoint deserialize_tree_shape' (acc : list (list (tree unit))) (l : list bool) :
    option (tree unit * list bool) :=
    match l with
    | [] => None
    | b :: l =>
      if b
      then match acc with
           | [] => Some (atom tt, l)
           | ts :: acc =>
             (* no need to call atomic deserializer, so recursion is structural! *)
             deserialize_tree_shape' ((atom tt :: ts) :: acc) l
           end
      else match l with
           | [] => None
           | b :: l =>
             if b
             then deserialize_tree_shape' ([] :: acc) l
             else match acc with
                  | [] => None
                  | ts :: acc => let t := node (List.rev ts) in
                              match acc with
                              | [] => Some (t, l)
                              | ts :: acc => deserialize_tree_shape' ((t :: ts) :: acc) l
                              end
                  end
           end
    end.

  (* Serializing and then deserializing the shape of a tree 't' is the same
     as `map (fun _ => tt) t`. *)

  (* We strengthen this statement to account for the accumulator. *)
  Lemma serialize_deserialize_shape'_id :
    forall t acc bin,
      deserialize_tree_shape' acc (serialize_tree_shape t ++ bin) =
      match acc with
      | [] => Some (map (fun _ => tt) t, bin)
      | j :: js => deserialize_tree_shape' ((map (fun _ => tt) t :: j) :: js) bin
      end.
  Proof.
    induction t using tree_rect with
    (P_list := fun l =>
       (* We need to extend the statement to a list of subtrees for the mutual induction
          hypothesis.
          It says that serializing and then deserializing a list of trees `l` is the same
          as `List.map (map (fun _ => tt) l)`.
          `deserialize_list_tree_shape'` is always called with at least one element on the
          accumulator, so there's no need for a match like there was above.
        *)
       forall ts acc bin,
         deserialize_tree_shape' (ts :: acc) (serialize_list_tree_shape l ++ bin) =
         deserialize_tree_shape' ((List.rev (List.map (map (fun _ => tt)) l) ++ ts) :: acc) bin);
    intros.
    - auto.
    - simpl. rewrite app_ass.
      rewrite IHt.
      rewrite IHt0.
      rewrite app_ass. auto.
    - auto.
    - simpl. fold serialize_list_tree_shape.
      rewrite app_ass.
      rewrite IHt.
      simpl.
      now rewrite app_nil_r, rev_involutive.
  Qed.

  Definition deserialize_tree_shape := deserialize_tree_shape' [].

  (* This is the top level statement about serializing and deserializing tree shapes:
     it results in `map (fun _ => tt)` of the original tree. *)
  Lemma serialize_deserialize_shape_id :
    forall t bin,
      deserialize_tree_shape (serialize_tree_shape t ++ bin) = Some (map (fun _ => tt) t, bin).
  Proof.
    unfold deserialize_tree_shape.
    intros.
    now rewrite serialize_deserialize_shape'_id.
  Qed.

  (* Now we serialize the tree itself by first serializing the shape, and then a
     preorder traversal of the elements. *)
  Definition tree_serialize (t : tree A) : list bool :=
    serialize_tree_shape t ++ serialize (preorder t).

  (* To deserialize, we deserialize the shape and the elements, and then fill out
     the shape with the elements. *)
  Definition tree_deserialize : deserializer (tree A) :=
    shape <- deserialize_tree_shape ;;
    elems <- deserialize ;;
    match fill shape elems with
    | None => fail
    | Some t => ret t
    end.

  (* To prove this correct, we need to know that serializ-/deserializing the shape of `t`
     results in `map (fun _ => tt) t` (`serialize_deserialize_shape_id`), and that
     filling out a `map f t` with the elements of `preorder t` results in `t`
     (`fill_preorder`).
   *)
  Lemma tree_serialize_deserialize_id :
    serialize_deserialize_id_spec tree_serialize tree_deserialize.
  Proof.
    unfold tree_serialize, tree_deserialize.
    serialize_deserialize_id_crush.
    rewrite serialize_deserialize_shape_id.
    serialize_deserialize_id_crush.
    now rewrite fill_preorder.
  Qed.

  Global Instance tree_Serializer : Serializer (tree A) :=
    {| serialize := tree_serialize;
        deserialize := tree_deserialize;
        serialize_deserialize_id := tree_serialize_deserialize_id
    |}.
End serializer.
