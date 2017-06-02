
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    Igroup

    Build the group of the inversible elements for the operation

    Definition: ZpGroup
  **********************************************************************)
Require Import ZArith.
Require Import Tactic.
Require Import Wf_nat.
Require Import UList.
Require Import ListAux.
Require Import FGroup.

Open Scope Z_scope.

Section IG.

Variable A: Set.
Variable op: A -> A -> A.
Variable support: list A.
Variable e: A.

Hypothesis A_dec: forall a b: A, {a = b} + {a <> b}.
Hypothesis support_ulist: ulist support.
Hypothesis e_in_support: In e support.
Hypothesis op_internal: forall a b, In a support -> In b support -> In (op a b) support.
Hypothesis op_assoc: forall a b c, In a support -> In b support -> In c support -> op a (op b c) = op (op a b) c.
Hypothesis e_is_zero_l:  forall a, In a support ->  op e a = a.
Hypothesis e_is_zero_r:  forall a, In a support ->  op a e = a.

(**************************************
  is_inv_aux tests if there is an inverse of a for op in l
 **************************************)

Fixpoint is_inv_aux (l: list A) (a: A) {struct l}: bool :=
  match l with nil => false | cons b l1 =>
   if (A_dec (op a b) e) then if (A_dec (op b a) e) then true else is_inv_aux l1 a else is_inv_aux l1 a
  end.

Theorem is_inv_aux_false: forall b l, (forall a, (In a l) -> op b a <> e \/  op a b <> e) -> is_inv_aux l b = false.
intros b l; elim l; simpl; auto.
intros a l1 Rec H; case (A_dec (op a b) e); case (A_dec (op b a) e); auto.
intros H1 H2; case (H a); auto; intros H3; case H3; auto.
Qed.

(**************************************
  is_inv tests if there is an inverse in support
 **************************************)
Definition is_inv := is_inv_aux support.

(**************************************
  isupport_aux returns the sublist of inversible element of support
 **************************************)

Fixpoint isupport_aux (l: list A) : list  A :=
  match l with nil => nil | cons a  l1 => if is_inv a then a::isupport_aux l1 else isupport_aux l1 end.

(**************************************
  Some properties of isupport_aux
 **************************************)

Theorem isupport_aux_is_inv_true: forall l a, In a (isupport_aux l) -> is_inv a = true.
intros l a; elim l; simpl; auto.
intros b l1 H; case_eq (is_inv b); intros H1; simpl; auto.
intros [H2 | H2]; subst; auto.
Qed.

Theorem isupport_aux_is_in: forall l a,  is_inv a = true -> In a l -> In a (isupport_aux l).
intros l a; elim l; simpl; auto.
intros b l1 Rec H [H1 | H1]; subst.
rewrite H; auto with datatypes.
case (is_inv b); auto with datatypes.
Qed.


Theorem isupport_aux_not_in:
  forall b l, (forall a, (In a support) -> op b a <> e \/  op a b <> e) -> ~ In b (isupport_aux l).
intros b l; elim l; simpl; simpl; auto.
intros a l1 H; case_eq (is_inv a); intros H1; simpl; auto.
intros H2 [H3 | H3]; subst.
contradict H1.
unfold is_inv; rewrite is_inv_aux_false; auto.
case H; auto; apply isupport_aux_is_in; auto.
Qed.

Theorem isupport_aux_incl: forall l, incl (isupport_aux l) l.
intros l; elim l; simpl; auto with datatypes.
intros a l1 H1; case (is_inv a); auto with datatypes.
Qed.

Theorem isupport_aux_ulist: forall l, ulist l -> ulist (isupport_aux l).
intros l; elim l; simpl; auto with datatypes.
intros a l1 H1 H2; case_eq (is_inv a); intros H3; auto with datatypes.
apply ulist_cons; auto with datatypes.
intros H4; apply (ulist_app_inv _ (a::nil) l1 a); auto with datatypes.
apply (isupport_aux_incl l1 a); auto.
apply H1; apply ulist_app_inv_r with (a:: nil); auto.
apply H1; apply ulist_app_inv_r with (a:: nil); auto.
Qed.

(**************************************
  isupport is the sublist of inversible element of support
 **************************************)

Definition isupport := isupport_aux support.

(**************************************
  Some properties of isupport
 **************************************)

Theorem isupport_is_inv_true: forall a, In a isupport -> is_inv a = true.
unfold isupport; intros a H; apply isupport_aux_is_inv_true with (1 := H).
Qed.

Theorem isupport_is_in: forall a,  is_inv a = true -> In a support -> In a isupport.
intros a H H1; unfold isupport; apply isupport_aux_is_in; auto.
Qed.

Theorem isupport_incl: incl isupport support.
unfold isupport; apply isupport_aux_incl.
Qed.

Theorem isupport_ulist: ulist isupport.
unfold isupport; apply isupport_aux_ulist.
apply support_ulist.
Qed.

Theorem isupport_length: (length isupport <= length support)%nat.
apply ulist_incl_length.
apply isupport_ulist.
apply isupport_incl.
Qed.

Theorem isupport_length_strict:
  forall b, (In b support) -> (forall a, (In a support) -> op b a <> e \/  op a b <> e) ->
           (length isupport < length support)%nat.
intros b H H1; apply ulist_incl_length_strict.
apply isupport_ulist.
apply isupport_incl.
intros H2; case (isupport_aux_not_in b support); auto.
Qed.

Fixpoint inv_aux (l: list A) (a: A) {struct l}: A :=
  match l with nil => e | cons b l1 =>
   if  A_dec (op a b) e then  if (A_dec (op b a) e) then b else inv_aux l1 a else inv_aux l1 a
  end.

Theorem inv_aux_prop_r: forall l a, is_inv_aux l a = true -> op a (inv_aux l a) = e.
intros l a; elim l; simpl.
intros; discriminate.
intros b l1 H1; case (A_dec (op a b) e); case (A_dec (op b a) e); intros H3 H4; subst; auto.
Qed.

Theorem inv_aux_prop_l: forall l a, is_inv_aux l a = true -> op (inv_aux l a) a = e.
intros l a; elim l; simpl.
intros; discriminate.
intros b l1 H1; case (A_dec (op a b) e); case (A_dec (op b a) e); intros H3 H4; subst; auto.
Qed.

Theorem inv_aux_inv: forall l a b, op a b = e -> op b a = e ->  (In a l) -> is_inv_aux l b = true.
intros l a b; elim l; simpl.
intros  _ _ H; case H.
intros c l1 Rec H H0 H1; case H1; clear H1; intros H1; subst;  rewrite H.
case (A_dec (op b a) e); case (A_dec e e); auto.
intros H1 H2; contradict H2; rewrite H0; auto.
case (A_dec (op b c) e); case (A_dec (op c b) e); auto.
Qed.

Theorem inv_aux_in: forall l a,  In (inv_aux l a) l \/ inv_aux l a = e.
intros l a; elim l; simpl; auto.
intros b l1; case (A_dec (op a b) e); case (A_dec (op b a) e); intros _ _ [H1 | H1]; auto.
Qed.

(**************************************
  The inverse function
 **************************************)

Definition inv := inv_aux support.

(**************************************
  Some properties of inv
 **************************************)

Theorem inv_prop_r: forall a, In a isupport -> op a (inv a) = e.
intros a H; unfold inv; apply inv_aux_prop_r with (l := support).
change (is_inv a = true).
apply isupport_is_inv_true; auto.
Qed.

Theorem inv_prop_l: forall a, In a isupport -> op (inv a) a = e.
intros a H; unfold inv; apply inv_aux_prop_l with (l := support).
change (is_inv a = true).
apply isupport_is_inv_true; auto.
Qed.

Theorem is_inv_true: forall a b, op b a = e ->  op a b = e -> (In a support) -> is_inv b = true.
intros a b H H1 H2; unfold is_inv; apply inv_aux_inv with a; auto.
Qed.

Theorem is_inv_false: forall b, (forall a, (In a support) -> op b a <> e \/  op a b <> e) -> is_inv b = false.
intros b H; unfold is_inv; apply is_inv_aux_false; auto.
Qed.

Theorem inv_internal: forall a, In a isupport -> In (inv a) isupport.
intros a H; apply isupport_is_in.
apply is_inv_true with a; auto.
apply inv_prop_l; auto.
apply inv_prop_r; auto.
apply (isupport_incl a); auto.
case (inv_aux_in support a); unfold inv; auto.
intros H1; rewrite H1; apply e_in_support; auto with zarith.
Qed.

(**************************************
   We are now ready to build our group
 **************************************)

Definition IGroup : (FGroup op).
generalize (fun x=> (isupport_incl x)); intros Hx.
apply mkGroup with (s := isupport) (e := e) (i := inv); auto.
apply isupport_ulist.
intros a b H H1.
assert (Haii: In (inv a) isupport); try apply  inv_internal; auto.
assert (Hbii: In (inv b) isupport); try apply  inv_internal; auto.
apply isupport_is_in; auto.
apply is_inv_true with (op (inv b) (inv a)); auto.
rewrite op_assoc; auto.
rewrite <- (op_assoc a); auto.
rewrite inv_prop_r; auto.
rewrite e_is_zero_r; auto.
apply inv_prop_r; auto.
rewrite <- (op_assoc (inv b)); auto.
rewrite  (op_assoc (inv a)); auto.
rewrite inv_prop_l; auto.
rewrite e_is_zero_l; auto.
apply inv_prop_l; auto.
apply isupport_is_in; auto.
apply is_inv_true with e; auto.
intros a H; apply inv_internal; auto.
intros; apply inv_prop_l; auto.
intros; apply inv_prop_r; auto.
Defined.

End IG.
