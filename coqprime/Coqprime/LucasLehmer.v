
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    LucasLehamer.v

    Build the sequence for the primality test of Mersenne numbers

    Definition: LucasLehmer
  **********************************************************************)
Require Import ZArith.
Require Import ZCAux.
Require Import Tactic.
Require Import Wf_nat.
Require Import NatAux.
Require Import UList.
Require Import ListAux.
Require Import FGroup.
Require Import EGroup.
Require Import PGroup.
Require Import IGroup.

Open Scope Z_scope.

(**************************************
  The seeds of the serie
 **************************************)

Definition w := (2, 1).

Definition v := (2, -1).

Theorem w_plus_v: pplus w v = (4, 0).
simpl; auto.
Qed.

Theorem w_mult_v : pmult w v = (1, 0).
simpl; auto.
Qed.

(**************************************
  Definition of the power function for pairs p^n
 **************************************)

Definition ppow p n := match n with  Zpos q => iter_pos _ (pmult p) (1, 0) q | _ => (1, 0) end.

(**************************************
  Some properties of ppow
 **************************************)

Theorem ppow_0: forall n, ppow n 0 = (1, 0).
simpl; auto.
Qed.

Theorem ppow_1: forall n, ppow (1, 0) n = (1, 0).
intros n; case n; simpl; auto.
intros p; apply iter_pos_invariant with (Inv := fun x => x = (1, 0)); auto.
intros x H; rewrite H; auto.
Qed.

Theorem ppow_op: forall a b p, iter_pos _ (pmult a) b p = pmult (iter_pos _ (pmult a) (1, 0) p) b.
intros a b p; generalize b; elim p; simpl; auto; clear  b p.
intros p Rec b.
rewrite (Rec b).
try rewrite (fun x y => Rec (pmult x y)); try rewrite (fun x y => Rec (iter_pos _ x y p)); auto.
repeat rewrite pmult_assoc; auto.
intros p Rec b.
rewrite (Rec b); try rewrite (fun x y => Rec (pmult x y)); try rewrite (fun x y => Rec (iter_pos _ x y p)); auto.
repeat rewrite pmult_assoc; auto.
intros b; rewrite pmult_1_r; auto.
Qed.

Theorem ppow_add: forall n m p, 0 <= m -> 0 <= p ->  ppow n (m + p) = pmult (ppow n m) (ppow n p).
intros n m; case m; clear m.
intros p _ _; rewrite ppow_0; rewrite pmult_1_l; auto.
2: intros p m H; contradict H; auto with zarith.
intros p1 m _; case m.
intros _; rewrite Zplus_0_r; simpl; apply sym_equal; apply pmult_1_r.
2: intros p2 H; contradict H; auto with zarith.
intros p2 _; simpl.
rewrite iter_pos_plus.
rewrite ppow_op; auto.
Qed.

Theorem ppow_ppow: forall n m p, 0 <= n -> 0 <= m -> ppow p (n * m ) = ppow (ppow p n) m.
intros n m; case n.
intros p _ Hm; rewrite Zmult_0_l.
rewrite ppow_0; apply sym_equal; apply ppow_1.
2: intros p p1 H; contradict H; auto with zarith.
intros p1 p _; case m; simpl; auto.
intros p2 _;  pattern p2; apply Pind; simpl; auto.
rewrite Pmult_1_r; rewrite pmult_1_r; auto.
intros p3 Rec; rewrite Pplus_one_succ_r; rewrite Pmult_plus_distr_l.
rewrite Pmult_1_r.
simpl; repeat rewrite iter_pos_plus; simpl.
rewrite pmult_1_r.
rewrite ppow_op; try rewrite Rec; auto.
apply sym_equal; apply ppow_op; auto.
Qed.


Theorem ppow_mult: forall n m p, 0 <= n -> ppow (pmult m p) n = pmult (ppow m n) (ppow p n).
intros n m p; case n; simpl; auto.
intros p1 _; pattern p1; apply Pind; simpl; auto.
repeat rewrite pmult_1_r; auto.
intros p3 Rec; rewrite Pplus_one_succ_r.
repeat rewrite iter_pos_plus; simpl.
repeat rewrite (fun x y z => ppow_op x (pmult y z)) ; auto.
rewrite Rec.
repeat rewrite pmult_1_r; auto.
repeat rewrite <- pmult_assoc; try eq_tac; auto.
rewrite (fun x y => pmult_comm (iter_pos _ x y p3) p); auto.
rewrite (pmult_assoc m); try apply pmult_comm; auto.
Qed.

(**************************************
  We can now define our series of pairs s
 **************************************)

Definition s n := pplus (ppow w (2 ^ n)) (ppow v (2 ^ n)).

(**************************************
  Some properties of s
 **************************************)

Theorem s0 : s 0 = (4, 0).
simpl; auto.
Qed.

Theorem sn_aux: forall n, 0 <= n -> s (n+1) = (pplus (pmult (s n) (s n)) (-2, 0)).
intros n Hn.
assert (Hu: 0 <= 2 ^n); auto with zarith.
set (y := (fst (s n) * fst (s n) - 2, 0)).
unfold s; simpl; rewrite Zpower_exp; auto with zarith.
rewrite Zpower_1_r; rewrite ppow_ppow; auto with zarith.
repeat rewrite pplus_pmult_dist_r || rewrite pplus_pmult_dist_l.
repeat rewrite <- pplus_assoc.
eq_tac; auto.
pattern 2 at 2; replace 2 with (1 + 1); auto with zarith.
rewrite ppow_add; auto with zarith; simpl.
rewrite pmult_1_r; auto.
rewrite Zmult_comm; rewrite ppow_ppow; simpl; auto with zarith.
repeat rewrite <- ppow_mult; auto with zarith.
rewrite (pmult_comm v w); rewrite w_mult_v.
rewrite ppow_1.
repeat rewrite tpower_1.
rewrite pplus_comm; repeat rewrite <- pplus_assoc;
rewrite pplus_comm; repeat rewrite <- pplus_assoc.
simpl; case (ppow (7, -4) (2 ^n)); simpl; intros z1 z2; eq_tac; auto with zarith.
Qed.

Theorem sn_snd: forall n, snd (s n) = 0.
intros n; case n; simpl; auto.
intros p; pattern p; apply Pind; auto.
intros p1 H; rewrite Zpos_succ_morphism; unfold Zsucc.
rewrite sn_aux; auto with zarith.
generalize H; case (s (Zpos p1)); simpl.
intros x y H1; rewrite H1; auto with zarith.
Qed.

Theorem sn: forall n, 0 <= n -> s (n+1) = (fst (s n) * fst  (s n) -2, 0).
intros n Hn; rewrite sn_aux; generalize (sn_snd n); case (s n); auto.
intros x y H; simpl in H; rewrite H; simpl.
eq_tac; ring.
Qed.

Theorem sn_w: forall n, 0 <= n ->  ppow w (2 ^ (n + 1)) = pplus (pmult (s n) (ppow w (2 ^ n))) (- 1, 0).
intros n H; unfold s; simpl; rewrite Zpower_exp; auto with zarith.
assert (Hu: 0 <= 2 ^n); auto with zarith.
rewrite Zpower_1_r; rewrite ppow_ppow; auto with zarith.
repeat rewrite pplus_pmult_dist_r || rewrite pplus_pmult_dist_l.
pattern 2 at 2; replace 2 with (1 + 1); auto with zarith.
rewrite ppow_add; auto with zarith; simpl.
rewrite pmult_1_r; auto.
repeat rewrite <- ppow_mult; auto with zarith.
rewrite (pmult_comm v w); rewrite w_mult_v.
rewrite ppow_1; simpl.
simpl; case (ppow (7, 4) (2 ^n)); simpl; intros z1 z2; eq_tac; auto with zarith.
Qed.

Theorem sn_w_next: forall n, 0 <= n ->  ppow w (2 ^ (n + 1)) = pplus (pmult (s n) (ppow w (2 ^ n))) (- 1, 0).
intros n H; unfold s; simpl; rewrite Zpower_exp; auto with zarith.
assert (Hu: 0 <= 2 ^n); auto with zarith.
rewrite Zpower_1_r; rewrite ppow_ppow; auto with zarith.
repeat rewrite pplus_pmult_dist_r || rewrite pplus_pmult_dist_l.
pattern 2 at 2; replace 2 with (1 + 1); auto with zarith.
rewrite ppow_add; auto with zarith; simpl.
rewrite pmult_1_r; auto.
repeat rewrite <- ppow_mult; auto with zarith.
rewrite (pmult_comm v w); rewrite w_mult_v.
rewrite ppow_1; simpl.
simpl; case (ppow (7, 4) (2 ^n)); simpl; intros z1 z2; eq_tac; auto with zarith.
Qed.

Section Lucas.

Variable p: Z.

(**************************************
  Definition of the mersenne number
 **************************************)

Definition Mp := 2^p -1.

Theorem mersenne_pos:  1 < p -> 1 < Mp.
intros H; unfold Mp; assert (2 < 2 ^p); auto with zarith.
apply Zlt_le_trans with (2^2); auto with zarith.
refine (refl_equal _).
apply Zpower_le_monotone; auto with zarith.
Qed.

Hypothesis p_pos2: 2 < p.

(**************************************
  We suppose that the mersenne number divides s
 **************************************)

Hypothesis Mp_divide_sn: (Mp  | fst (s (p - 2))).

Variable q: Z.

(**************************************
  We take a divisor of Mp and shows that Mp <= q^2, hence Mp is prime
 **************************************)

Hypothesis q_divide_Mp: (q | Mp).

Hypothesis q_pos2: 2 < q.

Theorem q_pos: 1 < q.
apply Zlt_trans with (2 := q_pos2); auto with zarith.
Qed.

(**************************************
  The definition of the groups of inversible pairs
 **************************************)

Definition pgroup := PGroup q q_pos.

Theorem w_in_pgroup: (In w pgroup.(FGroup.s)).
generalize q_pos; intros HM.
generalize q_pos2; intros HM2.
assert (H0: 0 < q); auto with zarith.
simpl; apply isupport_is_in; auto.
assert (zpmult q w (2, q - 1) = (1, 0)).
unfold zpmult, w, pmult, base; repeat (rewrite Zmult_1_r || rewrite Zmult_1_l).
eq_tac.
apply trans_equal with ((3 * q + 1) mod q).
eq_tac; auto with zarith.
rewrite Zplus_mod; auto.
rewrite Zmult_mod; auto.
rewrite Z_mod_same; auto with zarith.
rewrite Zmult_0_r; repeat rewrite Zmod_small; auto with zarith.
apply trans_equal with (2 * q mod q).
eq_tac; auto with zarith.
apply Zdivide_mod; auto with zarith; exists 2; auto with zarith.
apply is_inv_true with (2, q - 1); auto.
apply mL_in; auto with zarith.
intros; apply zpmult_1_l; auto with zarith.
intros; apply zpmult_1_r; auto with zarith.
rewrite zpmult_comm; auto.
apply mL_in; auto with zarith.
unfold w; apply mL_in; auto with zarith.
Qed.

Theorem e_order_divide_order: (e_order P_dec w pgroup | g_order pgroup).
apply e_order_divide_g_order.
apply w_in_pgroup.
Qed.

Theorem order_lt:  g_order pgroup < q * q.
unfold g_order, pgroup, PGroup; simpl.
rewrite <- (Zabs_eq (q * q)); auto with zarith.
rewrite <- (inj_Zabs_nat (q * q)); auto with zarith.
rewrite <- mL_length; auto with zarith.
apply inj_lt; apply isupport_length_strict with (0, 0).
apply mL_ulist.
apply mL_in; auto with zarith.
intros a _; left; rewrite zpmult_0_l; auto with zarith.
intros; discriminate.
Qed.

(**************************************
  The power function zpow: a^n
 **************************************)

Definition zpow a := gpow a pgroup.

(**************************************
  Some properties of zpow
 **************************************)

Theorem zpow_def:
  forall a b, In a pgroup.(FGroup.s) -> 0 <= b ->
     zpow a b = ((fst (ppow a b)) mod q, (snd (ppow a b)) mod q).
generalize q_pos; intros HM.
generalize q_pos2; intros HM2.
assert (H0: 0 < q); auto with zarith.
intros a b Ha Hb; generalize Hb; pattern b; apply natlike_ind; auto.
intros _; repeat rewrite Zmod_small; auto with zarith.
rewrite ppow_0; simpl; auto with zarith.
unfold zpow; intros n1 H Rec _; unfold Zsucc.
rewrite gpow_add; auto with zarith.
rewrite ppow_add; simpl; try rewrite pmult_1_r; auto with zarith.
rewrite Rec; unfold zpmult; auto with zarith.
case (ppow a n1); case a; unfold pmult, fst, snd.
intros x y z t.
repeat (rewrite Zmult_1_r || rewrite Zmult_0_r || rewrite Zplus_0_r || rewrite Zplus_0_l); eq_tac.
repeat rewrite (fun u v => Zplus_mod (u * v)); auto.
eq_tac; try eq_tac; auto.
repeat rewrite (Zmult_mod z); auto with zarith.
repeat rewrite (fun u v => Zmult_mod (u * v)); auto.
eq_tac; try eq_tac; auto with zarith.
repeat rewrite (Zmult_mod base); auto with zarith.
eq_tac; try eq_tac; auto with zarith.
apply Zmod_mod; auto.
apply Zmod_mod; auto.
repeat rewrite (fun u v => Zplus_mod (u * v)); auto.
eq_tac; try eq_tac; auto.
repeat rewrite (Zmult_mod z); auto with zarith.
repeat rewrite (Zmult_mod t); auto with zarith.
Qed.

Theorem zpow_w_n_minus_1: zpow w (2 ^ (p - 1)) = (-1 mod q, 0).
generalize q_pos; intros HM.
generalize q_pos2; intros HM2.
assert (H0: 0 < q); auto with zarith.
rewrite zpow_def.
replace (p - 1) with ((p - 2) + 1); auto with zarith.
rewrite sn_w; auto with zarith.
generalize Mp_divide_sn (sn_snd (p - 2)); case (s (p -2)); case (ppow w (2 ^ (p -2))).
unfold fst, snd; intros x y z t H1 H2; unfold pmult, pplus; subst.
repeat (rewrite Zmult_0_l || rewrite Zmult_0_r || rewrite Zplus_0_l || rewrite Zplus_0_r).
assert (H2: z mod q = 0).
case H1; intros q1 Hq1; rewrite Hq1.
case q_divide_Mp; intros q2 Hq2; rewrite Hq2.
rewrite Zmult_mod; auto.
rewrite (Zmult_mod q2); auto.
rewrite Z_mod_same; auto with zarith.
repeat (rewrite Zmult_0_r; rewrite (Zmod_small 0)); auto with zarith.
assert (H3:  forall x, (z * x) mod q = 0).
intros y1; rewrite Zmult_mod; try rewrite H2; auto.
assert (H4:  forall x y,  (z * x +  y) mod q = y mod q).
intros x1 y1; rewrite Zplus_mod; try rewrite H3; auto.
rewrite Zplus_0_l; apply Zmod_mod; auto.
eq_tac; auto.
apply w_in_pgroup.
apply Zlt_le_weak; apply Zpower_gt_0; auto with zarith.
Qed.

Theorem zpow_w_n: zpow w (2 ^ p) = (1, 0).
generalize q_pos; intros HM.
generalize q_pos2; intros HM2.
assert (H0: 0 < q); auto with zarith.
replace p with ((p - 1) + 1); auto with zarith.
rewrite Zpower_exp; try rewrite Zpower_exp_1; auto with zarith.
unfold zpow; rewrite gpow_gpow; auto with zarith.
generalize zpow_w_n_minus_1; unfold zpow; intros H1; rewrite H1; clear H1.
simpl; unfold zpmult, pmult.
repeat (rewrite Zmult_0_l || rewrite Zmult_0_r || rewrite Zplus_0_l ||
              rewrite Zplus_0_r || rewrite Zmult_1_r).
eq_tac; auto.
pattern (-1 mod q) at 1; rewrite <- (Zmod_mod (-1) q); auto with zarith.
repeat rewrite <- Zmult_mod; auto.
rewrite Zmod_small; auto with zarith.
apply w_in_pgroup.
Qed.

(**************************************
  As e = (1, 0), the previous equation implies that the order of the group divide 2^p
 **************************************)

Theorem e_order_divide_pow: (e_order P_dec w pgroup | 2 ^ p).
generalize q_pos; intros HM.
generalize q_pos2; intros HM2.
assert (H0: 0 < q); auto with zarith.
apply e_order_divide_gpow.
apply w_in_pgroup.
apply Zlt_le_weak; apply Zpower_gt_0; auto with zarith.
exact zpow_w_n.
Qed.

(**************************************
  So it is less than equal
 **************************************)

Theorem e_order_le_pow : e_order P_dec w pgroup <= 2 ^ p.
apply Zdivide_le.
apply Zlt_le_weak; apply e_order_pos.
apply Zpower_gt_0; auto with zarith.
apply e_order_divide_pow.
Qed.

(**************************************
  So order(w) must be 2^q
 **************************************)

Theorem e_order_eq_pow:  exists q, (e_order P_dec w pgroup)  = 2 ^ q.
case (Zdivide_power_2 (e_order P_dec w pgroup) 2 p); auto with zarith.
apply Zlt_le_weak; apply e_order_pos.
apply prime_2.
apply e_order_divide_pow; auto.
intros x H; exists x; auto with zarith.
Qed.

(**************************************
  Buth this q can only be p otherwise it would contradict w^2^(p -1) = (-1, 0)
 **************************************)

Theorem e_order_eq_p: e_order P_dec w pgroup = 2 ^ p.
case (Zdivide_power_2 (e_order P_dec w pgroup) 2 p); auto with zarith.
apply Zlt_le_weak; apply e_order_pos.
apply prime_2.
apply e_order_divide_pow; auto.
intros p1 Hp1.
case (Zle_lt_or_eq p1 p); try (intro H1; subst; auto; fail).
case (Zle_or_lt p1 p); auto; intros H1.
absurd (2 ^ p1 <= 2 ^ p); auto with zarith.
apply Zlt_not_le; apply Zpower_lt_monotone; auto with zarith.
apply Zdivide_le.
apply Zlt_le_weak; apply Zpower_gt_0; auto with zarith.
apply Zpower_gt_0; auto with zarith.
rewrite <- Hp1; apply e_order_divide_pow.
intros H1.
assert (Hu: 0 <= p1).
generalize Hp1; case p1; simpl; auto with zarith.
intros p2 Hu; absurd (0 < e_order  P_dec w pgroup).
rewrite Hu; auto with zarith.
apply e_order_pos.
absurd (zpow w (2 ^ (p - 1)) = (1, 0)).
rewrite zpow_w_n_minus_1.
intros H2; injection H2; clear H2; intros H2.
assert (H0: 0 < q); auto with zarith.
absurd (0 mod q = 0).
pattern 0 at 1; replace 0 with (-1 + 1); auto with zarith.
rewrite Zplus_mod; auto with zarith.
rewrite H2; rewrite (Zmod_small 1); auto with zarith.
rewrite Zmod_small; auto with zarith.
rewrite Zmod_small; auto with zarith.
unfold zpow; apply (gpow_pow _ _ w pgroup) with p1; auto with zarith.
apply w_in_pgroup.
rewrite <- Hp1.
apply (gpow_e_order_is_e _ P_dec _ w pgroup).
apply w_in_pgroup.
Qed.

(**************************************
  We have then the expected conclusion
 **************************************)

Theorem q_more_than_square:  Mp <  q * q.
unfold Mp.
assert (2 ^ p <= q * q); auto with zarith.
rewrite <- e_order_eq_p.
apply Zle_trans with (g_order pgroup).
apply Zdivide_le; auto with zarith.
apply Zlt_le_weak; apply e_order_pos; auto with zarith.
2: apply e_order_divide_order.
2: apply Zlt_le_weak; apply order_lt.
apply Zlt_le_trans with 2; auto with zarith.
replace 2 with (Z_of_nat (length ((1, 0)::w::nil))); auto.
unfold g_order; apply inj_le.
apply ulist_incl_length.
apply ulist_cons; simpl; auto.
unfold w; intros [H2 | H2];  try (case H2; fail); discriminate.
intro a; simpl; intros [H1 | [H1 | H1]]; subst.
assert (In (1, 0) (mL q)).
apply mL_in; auto with zarith.
apply isupport_is_in; auto.
apply is_inv_true with (1, 0); simpl; auto.
intros; apply zpmult_1_l; auto with zarith.
intros; apply zpmult_1_r; auto with zarith.
rewrite zpmult_1_r; auto with zarith.
rewrite zpmult_1_r; auto with zarith.
exact w_in_pgroup.
case H1.
Qed.

End Lucas.

(**************************************
  We build the sequence in Z
 **************************************)

Definition SS p :=
  let n := Mp p in
  match p - 2 with
    Zpos p1 => iter_pos _ (fun x => Zmodd (Zsquare x - 2) n) (Zmodd 4 n) p1
  | _ => (Zmodd 4 n)
  end.

Theorem SS_aux_correct:
  forall p z1 z2 n, 0 <= n -> 0 < z1 -> z2 = fst (s n) mod z1 ->
        iter_pos _ (fun x => Zmodd (Zsquare x - 2) z1) z2 p = fst (s (n + Zpos p)) mod z1.
intros p; pattern p; apply Pind.
simpl.
intros z1 z2 n Hn H H1; rewrite sn; auto; rewrite H1;  rewrite Zmodd_correct; rewrite Zsquare_correct; simpl.
unfold Zminus; rewrite Zplus_mod; auto.
rewrite (Zplus_mod (fst (s n) * fst (s n))); auto with zarith.
eq_tac; auto.
eq_tac; auto.
apply sym_equal; apply Zmult_mod; auto.
intros n Rec z1 z2 n1 Hn1 H1 H2.
rewrite Pplus_one_succ_l; rewrite iter_pos_plus.
rewrite Rec with (n0 := n1); auto.
replace (n1 + Zpos (1 + n)) with ((n1 + Zpos n) + 1); auto with zarith.
rewrite sn; simpl; try rewrite Zmodd_correct; try rewrite Zsquare_correct; simpl; auto with zarith.
unfold Zminus; rewrite Zplus_mod; auto.
unfold Zmodd.
rewrite (Zplus_mod (fst (s (n1 + Zpos n)) * fst (s (n1 + Zpos n)))); auto with zarith.
eq_tac; auto.
eq_tac; auto.
apply sym_equal; apply Zmult_mod; auto.
rewrite Zpos_plus_distr; auto with zarith.
Qed.

Theorem SS_prop: forall n, 1 < n -> SS n = fst(s (n -2)) mod (Mp n).
intros n Hn; unfold SS.
cut (0 <= n - 2); auto with zarith.
case (n - 2).
intros _; rewrite Zmodd_correct; rewrite s0; auto.
intros p1 H2; rewrite SS_aux_correct with (n := 0); auto with zarith.
apply Zle_lt_trans with 1; try apply mersenne_pos; auto with zarith.
rewrite Zmodd_correct; rewrite s0; auto.
intros p1 H2; case H2; auto.
Qed.

Theorem SS_prop_cor: forall p, 1 < p -> SS p = 0 -> (Mp p | fst(s (p -2))).
intros p H H1.
apply Zmod_divide.
generalize (mersenne_pos _ H); auto with zarith.
apply trans_equal with (2:= H1); apply sym_equal; apply SS_prop; auto.
Qed.

Theorem LucasLehmer:  forall p, 2 < p -> SS p = 0 -> prime (Mp p).
intros p H H1; case (prime_dec (Mp p)); auto; intros H2.
case Zdivide_div_prime_le_square with (2 := H2).
apply mersenne_pos; apply Zlt_trans with 2; auto with zarith.
intros q (H3, (H4, H5)).
contradict H5; apply Zlt_not_le.
apply q_more_than_square; auto.
apply SS_prop_cor; auto.
apply Zlt_trans with 2; auto with zarith.
case (Zle_lt_or_eq 2 q); auto.
apply prime_ge_2; auto.
intros H5; subst.
absurd (2 <= 1); auto with arith.
apply Zdivide_le; auto with zarith.
case H4; intros x Hx.
exists (2 ^ (p -1) - x).
rewrite Zmult_minus_distr_r; rewrite <- Hx; unfold Mp.
pattern 2 at 2; rewrite <- Zpower_1_r; rewrite <- Zpower_exp; auto with zarith.
replace (p - 1 + 1) with p; auto with zarith.
Qed.

(**************************************
  The test
 **************************************)

Definition lucas_test  n :=
   if Z_lt_dec 2 n then if Z_eq_dec (SS n) 0 then true else false else false.

Theorem LucasTest: forall n, lucas_test n = true -> prime (Mp n).
intros n; unfold lucas_test; case (Z_lt_dec 2 n); intros H1; try (intros; discriminate).
case (Z_eq_dec (SS n) 0); intros H2; try (intros; discriminate).
intros _; apply LucasLehmer; auto.
Qed.

Theorem prime7: prime 7.
exact (LucasTest 3 (refl_equal _)).
Qed.

Theorem prime31: prime 31.
exact (LucasTest 5 (refl_equal _)).
Qed.

Theorem prime127: prime 127.
exact (LucasTest 7 (refl_equal _)).
Qed.

Theorem prime8191: prime 8191.
exact (LucasTest 13 (refl_equal _)).
Qed.

Theorem prime131071: prime 131071.
exact (LucasTest 17 (refl_equal _)).
Qed.

Theorem prime524287: prime 524287.
exact (LucasTest 19 (refl_equal _)).
Qed.
