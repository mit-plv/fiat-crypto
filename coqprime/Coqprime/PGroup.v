
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    PGroup.v

    Build the group of pairs modulo needed for the theorem of
      lucas lehmer

    Definition: PGroup
 **********************************************************************)
Require Import ZArith.
Require Import Znumtheory.
Require Import Tactic.
Require Import Wf_nat.
Require Import ListAux.
Require Import UList.
Require Import FGroup.
Require Import EGroup.
Require Import IGroup.

Open Scope Z_scope.

Definition base := 3.


(**************************************
  Equality is decidable on pairs
 **************************************)

Definition P_dec: forall p q: Z * Z, {p = q} + {p <> q}.
intros p1 q1; case p1; case q1; intros z t x y; case (Z_eq_dec x z); intros H1.
case (Z_eq_dec y t); intros H2.
left; eq_tac; auto.
right; contradict H2; injection H2; auto.
right; contradict H1; injection H1; auto.
Defined.


(**************************************
  Addition of two pairs
 **************************************)

Definition pplus (p q: Z * Z) := let (x ,y) := p in let (z,t) := q in (x + z, y + t).

(**************************************
  Properties of addition
 **************************************)

Theorem pplus_assoc: forall p q r, (pplus p (pplus q r)) = (pplus (pplus p q) r).
intros p q r; case p; case q; case r; intros r1 r2 q1 q2 p1 p2; unfold pplus.
eq_tac; ring.
Qed.

Theorem pplus_comm: forall p q, (pplus p q) = (pplus q p).
intros p q; case p; case q; intros q1 q2 p1 p2; unfold pplus.
eq_tac; ring.
Qed.

(**************************************
  Multiplication of two pairs
 **************************************)

Definition pmult (p q: Z * Z) := let (x ,y) := p in let (z,t) := q in (x * z + base * y * t, x * t + y * z).

(**************************************
  Properties of multiplication
 **************************************)

Theorem pmult_assoc: forall p q r, (pmult p (pmult q r)) = (pmult (pmult p q) r).
intros p q r; case p; case q; case r; intros r1 r2 q1 q2 p1 p2; unfold pmult.
eq_tac; ring.
Qed.

Theorem pmult_0_l: forall p, (pmult (0, 0) p) = (0, 0).
intros p; case p; intros x y; unfold pmult; eq_tac; ring.
Qed.

Theorem pmult_0_r: forall p, (pmult p (0, 0)) = (0, 0).
intros p; case p; intros x y; unfold pmult; eq_tac; ring.
Qed.

Theorem pmult_1_l: forall p, (pmult (1, 0) p) = p.
intros p; case p; intros x y; unfold pmult; eq_tac; ring.
Qed.

Theorem pmult_1_r: forall p, (pmult p (1, 0)) = p.
intros p; case p; intros x y; unfold pmult; eq_tac; ring.
Qed.

Theorem pmult_comm: forall p q, (pmult p q) = (pmult q p).
intros p q; case p; case q; intros q1 q2 p1 p2; unfold pmult.
eq_tac; ring.
Qed.

Theorem pplus_pmult_dist_l: forall p q r, (pmult p (pplus q r)) = (pplus (pmult p q) (pmult p r)).
intros p q r; case p; case q; case r; intros r1 r2 q1 q2 p1 p2; unfold pplus, pmult.
eq_tac; ring.
Qed.


Theorem pplus_pmult_dist_r: forall p q r, (pmult (pplus q r) p) = (pplus (pmult q p) (pmult r p)).
intros p q r; case p; case q; case r; intros r1 r2 q1 q2 p1 p2; unfold pplus, pmult.
eq_tac; ring.
Qed.

(**************************************
  In this section we create the group PGroup of inversible elements {(p, q) | 0 <= p < m /\ 0 <= q < m}
 **************************************)
Section Mod.

Variable m : Z.

Hypothesis m_pos: 1 < m.

(**************************************
  mkLine creates {(a, p) | 0 <= p < n}
 **************************************)

Fixpoint mkLine (a: Z) (n: nat) {struct n} : list (Z * Z) :=
  (a, Z_of_nat n) :: match n with O => nil | (S n1) => mkLine a n1 end.

(**************************************
  Some properties of mkLine
 **************************************)

Theorem mkLine_length: forall a n, length (mkLine a n) = (n + 1)%nat.
intros a n; elim n; simpl; auto.
Qed.

Theorem mkLine_in: forall a n p, 0 <= p <= Z_of_nat n -> (In (a, p) (mkLine a n)).
intros a n; elim n.
simpl; auto with zarith.
intros p (H1, H2); replace p with 0; auto with zarith.
intros n1 Rec p (H1, H2).
case (Zle_lt_or_eq p  (Z_of_nat (S n1))); auto with zarith.
rewrite inj_S in H2; auto with zarith.
rewrite inj_S; auto with zarith.
intros H3; right; apply Rec; auto with zarith.
intros H3; subst; simpl; auto.
Qed.

Theorem in_mkLine: forall a n p, In p (mkLine  a n) ->  exists  q, 0 <= q <= Z_of_nat n  /\ p = (a, q).
intros a n p; elim n; clear n.
simpl; intros [H1 | H1]; exists 0; auto with zarith; case H1.
simpl; intros n Rec [H1 | H1]; auto.
exists (Z_of_nat (S n)); auto with zarith.
case Rec; auto; intros q ((H2, H3), H4); exists q; repeat split; auto with zarith.
change (q <= Z_of_nat (S n)).
rewrite inj_S; auto with zarith.
Qed.

Theorem mkLine_ulist: forall a n, ulist (mkLine a n).
intros a n; elim n; simpl; auto.
intros n1 H; apply ulist_cons; auto.
change (~ In (a, Z_of_nat (S n1)) (mkLine a n1)).
rewrite inj_S; intros H1.
case in_mkLine with (1 := H1); auto with zarith.
intros x ((H2, H3), H4); injection H4.
intros H5; subst; auto with zarith.
Qed.

(**************************************
  mkRect creates the list  {(p, q) | 0 <= p < n /\ 0 <= q < m}
 **************************************)

Fixpoint mkRect (n m: nat) {struct n} : list (Z * Z) :=
  (mkLine (Z_of_nat n) m) ++ match n with O => nil | (S n1) => mkRect n1 m end.

(**************************************
  Some properties of mkRect
 **************************************)

Theorem mkRect_length: forall n m, length (mkRect n m) = ((n + 1) * (m + 1))%nat.
intros n; elim n; simpl; auto.
intros n1; rewrite <- app_nil_end; rewrite mkLine_length; rewrite plus_0_r; auto.
intros n1 Rec m1; rewrite length_app; rewrite Rec; rewrite mkLine_length; auto.
Qed.

Theorem mkRect_in: forall n m p q, 0 <= p <= Z_of_nat n -> 0 <= q <= Z_of_nat m -> (In (p, q) (mkRect n m)).
intros n m1; elim n; simpl.
intros p  q  (H1, H2) (H3, H4); replace p with 0; auto with zarith.
rewrite <- app_nil_end; apply mkLine_in; auto.
intros n1 Rec p q (H1, H2) (H3, H4).
case (Zle_lt_or_eq p  (Z_of_nat (S n1))); auto with zarith; intros H5.
rewrite inj_S in H5; apply in_or_app; auto with zarith.
apply in_or_app; left; subst; apply mkLine_in; auto with zarith.
Qed.

Theorem in_mkRect: forall n m p, In p (mkRect n  m) ->  exists p1, exists  p2, 0 <= p1 <= Z_of_nat n  /\ 0 <= p2 <= Z_of_nat m  /\ p = (p1, p2).
intros n m1 p; elim n; clear n; simpl.
rewrite <- app_nil_end; intros H1.
case in_mkLine with (1 := H1).
intros p2 (H2, H3); exists 0; exists p2; auto with zarith.
intros n Rec H1.
case in_app_or with (1 := H1); intros H2.
case in_mkLine with (1 := H2).
intros p2 (H3, H4); exists (Z_of_nat (S n)); exists p2; subst; simpl; auto with zarith.
case Rec with (1 := H2); auto.
intros p1 (p2, (H3, (H4, H5))); exists p1; exists p2; repeat split; auto with zarith.
change (p1 <= Z_of_nat (S n)).
rewrite inj_S; auto with zarith.
Qed.

Theorem mkRect_ulist: forall n m, ulist (mkRect n m).
intros n; elim n; simpl; auto.
intros n1; rewrite <- app_nil_end; apply mkLine_ulist; auto.
intros n1 Rec m1; apply ulist_app; auto.
apply mkLine_ulist.
intros a H1 H2.
case in_mkLine with (1 := H1); intros p1 ((H3, H4), H5).
case in_mkRect with (1 := H2); intros p2 (p3, ((H6, H7), ((H8, H9), H10))).
subst; injection H10; clear H10; intros; subst.
contradict H7.
change (~ Z_of_nat (S n1) <= Z_of_nat  n1).
rewrite inj_S; auto with zarith.
Qed.

(**************************************
  mL is the list  {(p, q) | 0 <= p < m-1 /\ 0 <= q < m - 1}
 **************************************)
Definition mL := mkRect (Zabs_nat (m - 1)) (Zabs_nat (m -1)).

(**************************************
  Some properties of mL
 **************************************)

Theorem mL_length : length mL = Zabs_nat (m * m).
unfold mL; rewrite mkRect_length; simpl; apply inj_eq_rev.
repeat (rewrite inj_mult || rewrite inj_plus || rewrite inj_Zabs_nat || rewrite Zabs_eq); simpl; auto with zarith.
eq_tac; auto with zarith.
Qed.

Theorem mL_in: forall p q, 0 <= p < m -> 0 <= q <  m -> (In (p, q) mL).
intros p q (H1, H2) (H3, H4); unfold mL; apply mkRect_in; rewrite inj_Zabs_nat;
  rewrite Zabs_eq; auto with zarith.
Qed.

Theorem in_mL: forall p, In p mL->  exists p1, exists  p2, 0 <= p1 < m  /\ 0 <= p2 < m  /\ p = (p1, p2).
unfold mL; intros p H1; case in_mkRect with (1 := H1).
repeat (rewrite inj_Zabs_nat || rewrite Zabs_eq); auto with zarith.
intros p1 (p2, ((H2, H3), ((H4, H5), H6))); exists p1; exists p2; repeat split; auto with zarith.
Qed.

Theorem mL_ulist:  ulist mL.
unfold mL; apply mkRect_ulist; auto.
Qed.

(**************************************
  We define zpmult the multiplication of pairs module m
 **************************************)

Definition zpmult (p q: Z * Z) := let (x ,y) := pmult p q in (Zmod x m, Zmod y m).

(**************************************
  Some properties of zpmult
 **************************************)

Theorem zpmult_internal: forall p q, (In (zpmult p q) mL).
intros p q; unfold zpmult; case (pmult p q); intros z y; apply mL_in; auto with zarith.
apply Z_mod_lt; auto with zarith.
apply Z_mod_lt; auto with zarith.
Qed.

Theorem zpmult_assoc: forall p q r, (zpmult p (zpmult q r)) = (zpmult (zpmult p q) r).
assert (U: 0 < m); auto with zarith.
intros p q r; unfold zpmult.
generalize (pmult_assoc p q r).
case (pmult p q); intros x1 x2.
case (pmult q r); intros y1 y2.
case p; case r; unfold pmult.
intros z1 z2 t1 t2 H.
match goal with
  H: (?X, ?Y) = (?Z, ?T) |- _ =>
   assert (H1: X = Z); assert (H2: Y = T); try (injection H; simpl; auto; fail); clear H
end.
eq_tac.
generalize (f_equal (fun x => x mod m) H1).
repeat rewrite <- Zmult_assoc.
repeat (rewrite (fun x  => Zplus_mod (t1 * x))); auto.
repeat (rewrite (fun x  => Zplus_mod (x1 * x))); auto.
repeat (rewrite (fun x  => Zplus_mod (x1 mod m * x))); auto.
repeat (rewrite (Zmult_mod t1)); auto.
repeat (rewrite (Zmult_mod x1)); auto.
repeat (rewrite (Zmult_mod base)); auto.
repeat (rewrite (Zmult_mod t2)); auto.
repeat (rewrite (Zmult_mod x2)); auto.
repeat (rewrite (Zmult_mod (t2 mod m))); auto.
repeat (rewrite (Zmult_mod (x1 mod m))); auto.
repeat (rewrite (Zmult_mod (x2 mod m))); auto.
repeat (rewrite Zmod_mod); auto.
generalize (f_equal (fun x => x mod m) H2).
repeat (rewrite (fun x  => Zplus_mod (t1 * x))); auto.
repeat (rewrite (fun x  => Zplus_mod (x1 * x))); auto.
repeat (rewrite (fun x  => Zplus_mod (x1 mod m * x))); auto.
repeat (rewrite (Zmult_mod t1)); auto.
repeat (rewrite (Zmult_mod x1)); auto.
repeat (rewrite (Zmult_mod t2)); auto.
repeat (rewrite (Zmult_mod x2)); auto.
repeat (rewrite (Zmult_mod (t2 mod m))); auto.
repeat (rewrite (Zmult_mod (x1 mod m))); auto.
repeat (rewrite (Zmult_mod (x2 mod m))); auto.
repeat (rewrite Zmod_mod); auto.
Qed.

Theorem zpmult_0_l: forall p, (zpmult (0, 0) p) = (0, 0).
intros p; case p; intros x y; unfold zpmult, pmult; simpl.
rewrite Zmod_small; auto with zarith.
Qed.

Theorem zpmult_1_l: forall p, In p mL -> zpmult (1, 0) p = p.
intros p H; case in_mL with (1 := H); clear H; intros p1 (p2, ((H1, H2), (H3, H4))); subst.
unfold zpmult; rewrite pmult_1_l.
repeat rewrite Zmod_small; auto with zarith.
Qed.

Theorem zpmult_1_r: forall p, In p mL -> zpmult p (1, 0) = p.
intros p H; case in_mL with (1 := H); clear H; intros p1 (p2, ((H1, H2), (H3, H4))); subst.
unfold zpmult; rewrite pmult_1_r.
repeat rewrite Zmod_small; auto with zarith.
Qed.

Theorem zpmult_comm: forall p q, zpmult p q = zpmult q p.
intros p q; unfold zpmult; rewrite pmult_comm; auto.
Qed.

(**************************************
   We are now ready to build our group
 **************************************)

Definition PGroup : (FGroup zpmult).
apply IGroup with (support := mL) (e:= (1, 0)).
exact P_dec.
apply mL_ulist.
apply mL_in; auto with zarith.
intros; apply zpmult_internal.
intros; apply zpmult_assoc.
exact zpmult_1_l.
exact zpmult_1_r.
Defined.

End Mod.
