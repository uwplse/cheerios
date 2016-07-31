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

(* Our goal is now to give a Serializer for trees, given a Serializer for the
   data at the leaves.

   Converting a tree to a bitstream could be done naively as follows:
*)
Module naive_serializer.
  Variable A : Type.
  Context {sA : Serializer A}.

  Fixpoint tree_serialize (t : tree A) : list bool :=
    let fix list_tree_serialize (l : list (tree A)) : list bool :=
        match l with
        | [] => []
        | t :: l => tree_serialize t ++ list_tree_serialize l
        end
    in
    match t with
    | atom a =>
      (* think of [true] as ' from lisp, so this is 'a *)
      [true] ++ serialize a
    | node l =>
      (* think of [false; true] as ( and [false; false] as ) from lisp,
         so this is (t1 t2 .. tn) *)
      [false; true] ++ list_tree_serialize l ++ [false; false]
    end.

  (* A straightforward deserializer for this format would keep track of a stack
     of trees in the process of being constructed, ie, those subtrees where we've
     already processed the open parenthesis but not yet seen the corresponding
     close parenthesis. We can represent this stack as `list (list (tree A))`.
     The outer list is the stack. The inner list keeps track of all the siblings
     for that level that have already been processed.

     For example, if we're deserializing the representation of
           ('a ('b ('c) ('d) 'e) ('f 'g))
     and we're at the point in the stream just before 'e, then the stack would
     consist of
           [[['d]; ['c]; 'b]; ['a]]
     because we have two open parentheses (the one just before 'a and the one
     just before 'b), there are two elements on the stack. The bottom (rightmost)
     element consists of the completely processed subtrees of the outermost node,
     so far, just 'a. The top (leftmost) element consists of the completely
     processed subtrees of the node beginning with 'b, so far, just 'b, ['c], and
     ['d]. The next step would be to process 'e, cons it on to the top element of
     the stack, then process the close parenthesis, by forming a new node consisting
     of those subtrees in the top element of the stack (reversing the list), and
     consing it on to the next element on the stack, resulting in
           [[['b; ['c]; ['d]; 'e]; 'a]].
     This stack has one element, since there is only one open parenthesis. It
     consists of all the already processed subtrees for the outermost node.

     However, it is not clear how one would express this deserialization algorithm
     directly by structural recursion on the bitstream. The issue is that the
     deserializer processes cannot make any recursive call after calling any
     other deserializer, such as the atom's.

     More concretely, consider this illformed function:
   *)
  Fail
  Fixpoint tree_deserialize (acc : list (list (tree A))) (l : list bool) {struct l} :
        option (tree A * list bool) :=
    match l with
    | [] => None
    | b :: l =>
      if b
      then match deserialize l with None => None
           | Some (a, l) =>
             match acc with
             | [] => Some (atom a, l)
             | ts :: acc =>
               (* non-structural call on result of atom deserializer *)
               tree_deserialize ((atom a :: ts) :: acc) l
             end
           end
      else match l with
           | [] => None
           | b :: l =>
             if b
             then tree_deserialize ([] :: acc) l
             else match acc with
                  | [ts] => Some (node (rev ts), l)
                  | ts :: parent :: acc => tree_deserialize ((node (rev ts) :: parent) :: acc) l
                  | _ => None
                  end
           end
    end.

  (* In fact, a similar issue arises when deserializing lists. Cheerios solves
     the issue there by first serializing the length of the list (a natural
     number), and then the elements themselves.  The deserializer grabs the
     length and then deserializes that many elements. The key is that the
     recursive part of the deserializer goes by structural recursion on the
     *length*, not the bitsream.

     We are going to generalize this solution to trees as follows. Think of
     the length not as a natural number, but instead as a list of unit. Because
     the element type is trivial to deserialize, we don't run into the problem
     sketched above. Then, think of the list of elments as being used to
     "fill in" the places in the list of unit with the right values.

     We can now play the same game with trees. First, serialize the *shape*
     of the tree as a tree of unit. Then serialize the list of elements. To
     deserialize, deserialize the shape (no problem with structural recursion!)
     and then fill it out with the list of elements.
   *)
End naive_serializer.

(* The shape of a tree can be expressed by mapping (fun _ => tt) over it. *)
Section map.
  Variable A B : Type.
  Variable f : A -> B.

  Fixpoint map (t : tree A) : tree B :=
    match t with
    | atom a => atom (f a)
    | node l => node (List.map map l)
    end.
End map.

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
  match x with
  | atom a => [a]
  | node l => flat_map preorder l
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
       fill'_list (List.map (map f) l) (flat_map preorder l ++ bs) = Some (l, bs)); intros.
  - auto.
  - simpl.
    now rewrite app_ass, IHt, IHt0.
  - auto.
  - simpl.
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

  Fixpoint serialize_tree_shape (t : tree A) : list bool :=
    match t with
    | atom _ => [true] (* ignore the data, since we're just focused on the shape *)
    | node l => [false; true] ++ flat_map serialize_tree_shape l ++ [false; false]
    end.

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
         deserialize_tree_shape' (ts :: acc) (flat_map serialize_tree_shape l ++ bin) =
         deserialize_tree_shape' ((List.rev (List.map (map (fun _ => tt)) l) ++ ts) :: acc) bin);
    intros.
    - auto.
    - simpl. rewrite app_ass.
      rewrite IHt.
      rewrite IHt0.
      rewrite app_ass. auto.
    - auto.
    - simpl.
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

Module sexp.
  Import String.

  Definition sexp := tree string.

  Module examples.
    (*
       (define (id x) x)
    *)
    Definition id : sexp :=
      node [atom "define"; node [atom "id"; atom "x"]; atom "x"]%string.

    Eval compute in (eq_refl : deserialize (serialize id) = Some (id, [])).

    (*
       (define (Y f) ((lambda (x) (f (x x)))
                      (lambda (x) (f (x x)))))
    *)
    Definition Y : sexp :=
      node [atom "define"; node [atom "Y"; atom "f"];
          node [node [atom "lambda"; node [atom "x"]; node [atom "f"; node [atom "x"; atom "x"]]];
                node [atom "lambda"; node [atom "x"]; node [atom "f"; node [atom "x"; atom "x"]]]]]
           %string.

    Eval compute in (eq_refl : deserialize (serialize Y) = Some (Y, [])).
  End examples.
End sexp.

(* Here is a simple but complete example of how to use trees to more easily
   serialize user-defined types. *)
Module extended_example.
  Module expr.
    (* The untyped lambda calculus using de Bruijn indices. *)
    Inductive t : Type :=
    | Var : nat -> t
    | Lam : t -> t
    | App : t -> t -> t
    .
  End expr.

  (* Generally, the atoms of the tree will contain the constructor names and
     non-recursive arguments. *)
  Module tag.
    Inductive t : Type :=
    | Var (n : nat)
    | Lam
    | App
    .

    (* Tags should generally be easy to serialize, assuming all the non-recursive
       arguments are already serializable. *)
    Definition tag_serialize (x : t) : list bool :=
      match x with
      | Var n => serialize 0 ++ serialize n
      | Lam => serialize 1
      | App => serialize 2
      end.

    Import DeserializerNotations.

    Definition tag_deserialize : deserializer t :=
      n <- deserialize ;;
      match n with
      | 0 => Var <$> deserialize
      | 1 => ret Lam
      | 2 => ret App
      | _ => fail
      end.

    Lemma tag_serialize_deserialize_id :
      serialize_deserialize_id_spec tag_serialize tag_deserialize.
    Proof.
      unfold tag_serialize, tag_deserialize.
      destruct a; serialize_deserialize_id_crush.
    Qed.

    Instance tag_Serializer : Serializer t :=
      {| serialize := tag_serialize;
         deserialize := tag_deserialize;
         serialize_deserialize_id := tag_serialize_deserialize_id
      |}.
  End tag.

  (* With the tags in hand, it's easy to convert exprs to trees. *)
  Fixpoint expr_treeify (e : expr.t) : tree tag.t :=
    match e with
    | expr.Var n => atom (tag.Var n)
    | expr.Lam e => node [atom tag.Lam; expr_treeify e]
    | expr.App e1 e2 => node [atom tag.App; expr_treeify e1; expr_treeify e2]
    end.

  (* Converting a tree to an expr is also fairly straightforward, except that it
     can fail because the tree can be malformed. *)
  Fixpoint expr_untreeify (t : tree tag.t) : option expr.t :=
    match t with
    | atom (tag.Var n) => Some (expr.Var n)
    | node [atom tag.Lam; t] =>
      match expr_untreeify t with None => None
      | Some e => Some (expr.Lam e)
      end
    | node [atom tag.App; t1; t2] =>
      match expr_untreeify t1 with None => None
      | Some e1 =>
      match expr_untreeify t2 with None => None
      | Some e2 => Some (expr.App e1 e2)
      end end
    | _ => None
    end.

  Lemma expr_treeify_untreeify_id :
    forall e, expr_untreeify (expr_treeify e) = Some e.
  Proof.
    induction e; simpl.
    - auto.
    - now rewrite IHe.
    - now rewrite IHe1, IHe2.
  Qed.

  (* Now we can serialize an expr by converting to a tree and serializing it. *)
  Definition expr_serialize (e : expr.t) : list bool :=
    serialize (expr_treeify e).

  Import DeserializerNotations.
  Definition expr_deserialize : deserializer expr.t :=
    t <- deserialize ;;
    unwrap (expr_untreeify t).

  Lemma expr_serialize_deserialize_id :
    serialize_deserialize_id_spec expr_serialize expr_deserialize.
  Proof.
    unfold expr_serialize, expr_deserialize.
    serialize_deserialize_id_crush.
    now rewrite expr_treeify_untreeify_id.
  Qed.

  Instance expr_Serializer : Serializer expr.t :=
    {| serialize := expr_serialize;
       deserialize := expr_deserialize;
       serialize_deserialize_id := expr_serialize_deserialize_id
    |}.
End extended_example.
