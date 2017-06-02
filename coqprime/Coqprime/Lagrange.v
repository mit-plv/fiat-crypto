
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    Lagrange.v

    Proof of Lagrange theorem:
      the oder of a subgroup divides the order of a group

    Definition: lagrange
  **********************************************************************)
Require Import List.
Require Import UList.
Require Import ListAux.
Require Import ZArith Znumtheory.
Require Import NatAux.
Require Import FGroup.

Open Scope Z_scope.

Section Lagrange.

Variable A: Set.

Variable A_dec: forall a b: A, {a = b} + {~ a = b}.

Variable op: A -> A -> A.

Variable G: (FGroup op).

Variable H:(FGroup op).

Hypothesis G_in_H: (incl G.(s)  H.(s)).

(**************************************
   A group and a subgroup have the same neutral element
 **************************************)

Theorem same_e_for_H_and_G: H.(e) = G.(e).
apply trans_equal with (op H.(e) H.(e)); sauto.
apply trans_equal with (op H.(e) (op G.(e) (H.(i) G.(e)))); sauto.
eq_tac; sauto.
apply trans_equal with (op G.(e) (op G.(e) (H.(i) G.(e)))); sauto.
repeat rewrite  H.(assoc); sauto.
eq_tac; sauto.
apply trans_equal with G.(e); sauto.
apply trans_equal with (op G.(e) H.(e)); sauto.
eq_tac; sauto.
Qed.

(**************************************
   The proof works like this.
   If G = {e, g1, g2, g3, .., gn} and {e, h1, h2, h3, ..., hm}
   we construct the list mkGH
    {e, g1, g2, g3, ...., gn
     hi*e, hi * g1, hi * g2, ..., hi * gn   if hi does not appear before
     ....
     hk*e, hk * g1, hk * g2, ..., hk * gn   if hk does not appear before
     }
     that contains all the element of H.
   We show that this list does not contain double (ulist).
 **************************************)

Fixpoint mkList (base l: (list A)) { struct l}  : (list A) :=
  match l with
   nil => nil
 | cons a l1 => let r1 := mkList base l1 in
                         if (In_dec A_dec a r1) then r1 else
                          (map (op a) base) ++ r1
  end.

Definition mkGH := mkList G.(s) H.(s).

Theorem mkGH_length:  divide (length G.(s)) (length mkGH).
unfold mkGH; elim H.(s); simpl.
exists 0%nat; auto with arith.
intros a l1 (c, H1); case (In_dec A_dec a (mkList  G.(s) l1)); intros H2.
exists c; auto.
exists (1 + c)%nat; rewrite ListAux.length_app; rewrite ListAux.length_map; rewrite H1; ring.
Qed.

Theorem mkGH_incl: incl H.(s) mkGH.
assert (H1: forall l, incl l H.(s) -> incl l  (mkList G.(s) l)).
intros l; elim l; simpl; auto with datatypes.
intros a l1 H1 H2.
case  (In_dec A_dec a (mkList (s G) l1)); auto with datatypes.
intros H3; assert (H4: incl l1 (mkList (s G) l1)).
apply H1; auto with datatypes.
intros b H4; apply H2; auto with datatypes.
intros b; simpl; intros [H5 | H5]; subst; auto.
intros _ b; simpl; intros [H3 | H3]; subst; auto.
apply in_or_app; left.
cut (In H.(e) G.(s)).
elim (s G); simpl; auto.
intros c l2 Hl2 [H3 | H3]; subst; sauto.
assert (In b H.(s)); sauto.
apply (H2 b); auto with datatypes.
rewrite same_e_for_H_and_G; sauto.
apply in_or_app; right.
apply H1; auto with datatypes.
apply incl_tran with (2:= H2); auto with datatypes.
unfold mkGH; apply H1; auto with datatypes.
Qed.

Theorem incl_mkGH: incl mkGH H.(s).
assert (H1: forall l, incl l H.(s) -> incl (mkList G.(s) l) H.(s)).
intros l; elim l; simpl; auto with datatypes.
intros a l1 H1 H2.
case  (In_dec A_dec a (mkList (s G) l1)); intros H3; auto with datatypes.
apply H1; apply incl_tran with (2 := H2); auto with datatypes.
apply incl_app.
intros b H4.
case ListAux.in_map_inv with (1:= H4); auto.
intros c (Hc1, Hc2); subst; sauto.
apply internal; auto with datatypes.
apply H1; apply incl_tran with (2 := H2); auto with datatypes.
unfold mkGH; apply H1; auto with datatypes.
Qed.

Theorem ulist_mkGH: ulist mkGH.
assert (H1: forall l, incl l H.(s) -> ulist  (mkList G.(s) l)).
intros l; elim l; simpl; auto with datatypes.
intros a l1 H1 H2.
case  (In_dec A_dec a (mkList (s G) l1)); intros H3; auto with datatypes.
apply H1; apply incl_tran with (2 := H2); auto with datatypes.
apply ulist_app; auto.
apply ulist_map; sauto.
intros x y H4 H5 H6; apply g_cancel_l with (g:= H) (a := a); sauto.
apply H2; auto with datatypes.
apply H1; apply incl_tran with (2 := H2); auto with datatypes.
intros b H4 H5.
case ListAux.in_map_inv with (1:= H4); auto.
intros c (Hc, Hc1); subst.
assert (H6: forall l a b,  In b G.(s) -> incl l H.(s) -> In a (mkList G.(s) l) -> In (op a b) (mkList G.(s) l)).
intros ll u v; elim ll; simpl; auto with datatypes.
intros w ll1 T0 T1 T2.
case  (In_dec A_dec w (mkList (s G) ll1)); intros T3 T4; auto with datatypes.
apply T0; auto; apply incl_tran with (2:= T2); auto with datatypes.
case in_app_or with (1 := T4); intros T5; auto with datatypes.
apply in_or_app; left.
case ListAux.in_map_inv with (1:= T5); auto.
intros z (Hz1, Hz2); subst.
replace (op (op w z) v) with (op w (op z v)); sauto.
apply in_map; sauto.
apply assoc with H; auto with datatypes.
apply in_or_app; right; auto with datatypes.
apply T0; try apply incl_tran with (2 := T2); auto with datatypes.
case H3; replace a with (op  (op a c) (G.(i) c)); auto with datatypes.
apply H6; sauto.
apply incl_tran with (2 := H2); auto with datatypes.
apply trans_equal with (op a (op c (G.(i) c))); sauto.
apply sym_equal; apply assoc with H; auto with datatypes.
replace (op c (G.(i) c)) with (G.(e)); sauto.
rewrite <- same_e_for_H_and_G.
assert (In a H.(s)); sauto; apply (H2 a); auto with datatypes.
unfold mkGH; apply H1; auto with datatypes.
Qed.

(**************************************
  Lagrange theorem
 **************************************)

Theorem lagrange: (g_order G | (g_order H)).
unfold g_order.
rewrite Permutation.permutation_length with  (l := H.(s)) (m:= mkGH).
case mkGH_length; intros x H1; exists (Z_of_nat x).
rewrite H1; rewrite Zmult_comm; apply inj_mult.
apply ulist_incl2_permutation; auto.
apply ulist_mkGH.
apply mkGH_incl.
apply incl_mkGH.
Qed.

End Lagrange.
