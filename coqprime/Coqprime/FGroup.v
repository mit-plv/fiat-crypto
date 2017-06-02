
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    FGroup.v

    Defintion and properties of finite groups

    Definition: FGroup
  **********************************************************************)
Require Import List.
Require Import UList.
Require Import Tactic.
Require Import ZArith.

Open Scope Z_scope.

Set Implicit Arguments.

(**************************************
  A finite group is defined for an operation op
  it has a support  (s)
  op operates inside the group (internal)
  op is associative (assoc)
  it has an element (e) that is neutral (e_is_zero_l e_is_zero_r)
  it has an inverse operator (i)
  the inverse operates inside the group (i_internal)
  it gives an inverse (i_is_inverse_l is_is_inverse_r)
 **************************************)

Record FGroup (A: Set) (op: A -> A -> A): Set := mkGroup
  {s : (list A);
   unique_s: ulist s;
   internal: forall a b, In a s -> In b s -> In (op a b) s;
   assoc: forall a b c, In a s -> In b s -> In c s -> op a (op b c) = op (op a b) c;
   e: A;
   e_in_s: In e s;
   e_is_zero_l:  forall a, In a s ->  op e a = a;
   e_is_zero_r:  forall a, In a s ->  op a e = a;
   i: A -> A;
   i_internal: forall a, In a s -> In (i a) s;
   i_is_inverse_l:  forall a, (In a s) -> op (i a) a = e;
   i_is_inverse_r:  forall a, (In a s) -> op a (i a) = e
}.

(**************************************
   The order of a group is the lengh of the support
 **************************************)

Definition g_order  (A: Set) (op: A -> A -> A) (g: FGroup op)  := Z_of_nat (length g.(s)).

Unset Implicit Arguments.

Hint Resolve unique_s internal e_in_s e_is_zero_l e_is_zero_r i_internal
  i_is_inverse_l i_is_inverse_r assoc.


Section FGroup.

Variable A: Set.
Variable op: A -> A -> A.

(**************************************
   Some properties of a finite group
 **************************************)

Theorem g_cancel_l: forall (g : FGroup op), forall a b c, In a g.(s) -> In b g.(s) -> In c g.(s) -> op a b = op a c -> b = c.
intros g a b c H1 H2 H3 H4; apply trans_equal with (op g.(e) b); sauto.
replace (g.(e)) with (op (g.(i) a)  a); sauto.
apply trans_equal with (op (i g a) (op a b)); sauto.
apply sym_equal; apply assoc with g; auto.
rewrite H4.
apply trans_equal with (op (op  (i g a) a) c); sauto.
apply assoc with g; auto.
replace (op (g.(i) a)  a) with g.(e); sauto.
Qed.

Theorem g_cancel_r: forall (g : FGroup op), forall a b c, In a g.(s) -> In b g.(s) -> In c g.(s) -> op b a = op c a -> b = c.
intros g a b c H1 H2 H3 H4; apply trans_equal with (op b g.(e)); sauto.
replace (g.(e)) with (op a (g.(i) a)); sauto.
apply trans_equal with (op (op b  a) (i g a)); sauto.
apply assoc with g; auto.
rewrite H4.
apply trans_equal with (op c (op  a (i g a))); sauto.
apply sym_equal; apply assoc with g; sauto.
replace (op a (g.(i) a)) with g.(e); sauto.
Qed.

Theorem e_unique: forall (g : FGroup op), forall e1, In e1 g.(s) ->  (forall a, In a g.(s) -> op e1 a = a) -> e1 = g.(e).
intros g e1 He1 H2.
apply trans_equal with (op e1 g.(e)); sauto.
Qed.

Theorem inv_op: forall (g: FGroup op) a b, In a g.(s) -> In b g.(s) ->  g.(i) (op a b) = op (g.(i) b) (g.(i) a).
intros g a1 b1 H1 H2; apply g_cancel_l with (g := g) (a := op a1 b1); sauto.
repeat rewrite g.(assoc); sauto.
apply trans_equal with g.(e); sauto.
rewrite <- g.(assoc) with (a := a1); sauto.
rewrite g.(i_is_inverse_r); sauto.
rewrite g.(e_is_zero_r); sauto.
Qed.

Theorem i_e: forall (g: FGroup op), g.(i) g.(e) = g.(e).
intro g; apply g_cancel_l with (g:= g) (a := g.(e)); sauto.
apply trans_equal with g.(e); sauto.
Qed.

(**************************************
   A group has at least one element
 **************************************)

Theorem g_order_pos: forall g: FGroup op, 0 < g_order g.
intro g; generalize g.(e_in_s); unfold g_order; case g.(s); simpl; auto with zarith.
Qed.



End FGroup.
