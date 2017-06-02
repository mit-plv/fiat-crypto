
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
     Aux.v

     Auxillary functions & Theorems
 **********************************************************************)
Require Export Arith.

(**************************************
  Some properties of minus
**************************************)

Theorem minus_O : forall a b : nat, a <= b -> a - b = 0.
intros a; elim a; simpl in |- *; auto with arith.
intros a1 Rec b; case b; elim b; auto with arith.
Qed.


(**************************************
  Definitions and properties of the power for nat
**************************************)

Fixpoint pow (n m: nat)  {struct m} : nat := match m with O => 1%nat | (S m1) => (n * pow n m1)%nat  end.

Theorem pow_add: forall n m p, pow n (m + p) = (pow n m * pow n p)%nat.
intros n m; elim m; simpl.
intros p; rewrite plus_0_r; auto.
intros m1 Rec p; rewrite Rec; auto with arith.
Qed.


Theorem pow_pos: forall p n, (0 < p)%nat -> (0 < pow p n)%nat.
intros p1 n H; elim n; simpl; auto with arith.
intros n1 H1; replace 0%nat with (p1 * 0)%nat; auto with arith.
repeat rewrite (mult_comm p1); apply mult_lt_compat_r; auto with arith.
Qed.


Theorem pow_monotone: forall n p q, (1 < n)%nat -> (p < q)%nat -> (pow n p < pow n q)%nat.
intros n p1 q1 H H1; elim H1; simpl.
pattern (pow n p1) at 1; rewrite <- (mult_1_l (pow n p1)).
apply mult_lt_compat_r; auto.
apply pow_pos; auto with arith.
intros n1 H2 H3.
apply lt_trans with (1 := H3).
pattern (pow n n1) at 1; rewrite <- (mult_1_l (pow n n1)).
apply mult_lt_compat_r; auto.
apply pow_pos; auto with arith.
Qed.

(************************************
  Definition of the divisibility for nat
**************************************)

Definition divide a b := exists c, b = a * c.


Theorem divide_le: forall p q, (1 < q)%nat -> divide p q -> (p <= q)%nat.
intros p1 q1 H (x, H1); subst.
apply le_trans with (p1 * 1)%nat; auto with arith.
rewrite mult_1_r; auto with arith.
apply mult_le_compat_l.
case (le_lt_or_eq 0 x); auto with arith.
intros H2; subst; contradict H; rewrite mult_0_r; auto with arith.
Qed.
