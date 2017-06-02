
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    Zp.v

    Build the group of the inversible element on {1, 2, .., n-1}
    for the multiplication modulo n

    Definition: ZpGroup
 **********************************************************************)
Require Import ZArith Znumtheory Zpow_facts.
Require Import Tactic.
Require Import Wf_nat.
Require Import UList.
Require Import FGroup.
Require Import EGroup.
Require Import IGroup.
Require Import Cyclic.
Require Import Euler.
Require Import ZProgression.

Open Scope Z_scope.

Section Zp.

Variable n: Z.

Hypothesis n_pos: 1 < n.


(**************************************
  mkZp m creates {m, m - 1, ..., 0}
 **************************************)

Fixpoint mkZp_aux (m: nat): list Z:=
  Z_of_nat m :: match m with O => nil | (S m1) => mkZp_aux m1 end.

(**************************************
  Some properties of mkZp_aux
 **************************************)

Theorem mkZp_aux_length: forall m, length (mkZp_aux m) = (m + 1)%nat.
intros m; elim m; simpl; auto.
Qed.

Theorem mkZp_aux_in: forall m p, 0 <= p <= Z_of_nat m -> In p (mkZp_aux m).
intros m; elim m.
simpl; auto with zarith.
intros n1 Rec p (H1, H2); case Zle_lt_or_eq with (1 := H2); clear H2; intro H2.
rewrite inj_S in H2.
simpl; right; apply Rec; split; auto with zarith.
rewrite H2; simpl; auto.
Qed.

Theorem in_mkZp_aux: forall m p, In p (mkZp_aux  m) ->  0 <= p <= Z_of_nat m.
intros m; elim m; clear m.
simpl; intros p H1; case H1; clear H1; intros H1; subst; auto with zarith.
intros m1; generalize (inj_S m1); simpl.
intros H Rec p [H1 | H1].
rewrite <- H1; rewrite H; auto with zarith.
rewrite H; case (Rec p); auto with zarith.
Qed.

Theorem mkZp_aux_ulist: forall m, ulist (mkZp_aux m).
intros m; elim m; simpl; auto.
intros m1 H; apply ulist_cons; auto.
change (~ In (Z_of_nat (S m1)) (mkZp_aux m1)).
rewrite inj_S; intros H1.
case in_mkZp_aux with (1 := H1); auto with zarith.
Qed.

(**************************************
  mkZp creates {n - 1, ..., 1, 0}
 **************************************)

Definition mkZp := mkZp_aux (Zabs_nat (n - 1)).

(**************************************
  Some properties of mkZp
 **************************************)

Theorem mkZp_length: length mkZp = Zabs_nat n.
unfold mkZp; rewrite mkZp_aux_length.
apply inj_eq_rev.
rewrite inj_plus.
simpl; repeat rewrite inj_Zabs_nat; auto with zarith.
repeat rewrite Zabs_eq; auto with zarith.
Qed.

Theorem mkZp_in: forall p, 0 <= p < n -> In p mkZp.
intros p (H1, H2); unfold mkZp; apply mkZp_aux_in.
rewrite inj_Zabs_nat; auto with zarith.
repeat rewrite Zabs_eq; auto with zarith.
Qed.

Theorem in_mkZp: forall p, In p mkZp ->  0 <= p < n.
intros p H; case (in_mkZp_aux (Zabs_nat  (n - 1)) p); auto with zarith.
rewrite inj_Zabs_nat; auto with zarith.
repeat rewrite Zabs_eq; auto with zarith.
Qed.

Theorem mkZp_ulist: ulist mkZp.
unfold mkZp; apply mkZp_aux_ulist; auto.
Qed.

(**************************************
  Multiplication of two pairs
 **************************************)

Definition pmult (p q: Z) := (p * q) mod n.

(**************************************
  Properties of multiplication
 **************************************)

Theorem pmult_assoc: forall p q r, (pmult p (pmult q r)) = (pmult (pmult p q) r).
assert (Hu: 0 < n); try apply Zlt_trans with 1; auto with zarith.
generalize Zmod_mod; intros H.
intros p q r; unfold pmult.
rewrite (Zmult_mod p); auto.
repeat rewrite Zmod_mod; auto.
rewrite (Zmult_mod q); auto.
rewrite <- Zmult_mod; auto.
rewrite Zmult_assoc.
rewrite (Zmult_mod (p * (q mod n))); auto.
rewrite (Zmult_mod ((p * q) mod n)); auto.
eq_tac; auto.
eq_tac; auto.
rewrite (Zmult_mod p); sauto.
rewrite Zmod_mod; auto.
rewrite <- Zmult_mod; sauto.
Qed.

Theorem pmult_1_l: forall p, In p mkZp -> pmult 1 p = p.
intros p H; unfold pmult; rewrite Zmult_1_l.
apply Zmod_small.
case (in_mkZp p); auto with zarith.
Qed.

Theorem pmult_1_r: forall p, In p mkZp -> pmult p 1 = p.
intros p H; unfold pmult; rewrite Zmult_1_r.
apply Zmod_small.
case (in_mkZp p); auto with zarith.
Qed.

Theorem pmult_comm: forall p q, pmult p q = pmult q p.
intros p q; unfold pmult; rewrite Zmult_comm; auto.
Qed.

Definition Lrel := isupport_aux _ pmult  mkZp 1 Z_eq_dec (progression Zsucc 0 (Zabs_nat n)).

Theorem rel_prime_is_inv:
  forall a, is_inv Z pmult mkZp 1 Z_eq_dec a = if (rel_prime_dec a n) then true else false.
assert (Hu: 0 < n); try apply Zlt_trans with 1; auto with zarith.
intros a; case (rel_prime_dec a n); intros H.
assert (H1: Bezout a n 1); try apply rel_prime_bezout; auto.
inversion H1 as [c d Hcd]; clear H1.
assert (pmult (c mod n) a = 1).
unfold pmult; rewrite Zmult_mod; try rewrite Zmod_mod; auto.
rewrite <- Zmult_mod; auto.
replace (c * a) with (1 + (-d) * n).
rewrite Z_mod_plus; auto with zarith.
rewrite Zmod_small; auto with zarith.
rewrite <- Hcd; ring.
apply is_inv_true with (a := (c mod n)); auto.
apply mkZp_in; auto with zarith.
exact pmult_1_l.
exact pmult_1_r.
rewrite pmult_comm; auto.
apply mkZp_in; auto with zarith.
apply Z_mod_lt; auto with zarith.
apply is_inv_false.
intros c H1; left; intros H2; contradict H.
apply bezout_rel_prime.
apply Bezout_intro with c  (- (Zdiv (c * a) n)).
pattern (c * a) at 1; rewrite (Z_div_mod_eq (c * a) n); auto with zarith.
unfold pmult in H2; rewrite (Zmult_comm c); try rewrite H2.
ring.
Qed.

(**************************************
   We are now ready to build our group
 **************************************)

Definition ZPGroup : (FGroup pmult).
apply IGroup with (support := mkZp) (e:= 1).
exact Z_eq_dec.
apply mkZp_ulist.
apply mkZp_in; auto with zarith.
intros a b H1 H2; apply mkZp_in.
unfold pmult; apply Z_mod_lt; auto with zarith.
intros; apply pmult_assoc.
exact pmult_1_l.
exact pmult_1_r.
Defined.

Theorem in_ZPGroup: forall p, rel_prime p n -> 0 <= p < n -> In p ZPGroup.(s).
intros p H (H1, H2); unfold ZPGroup; simpl.
apply isupport_is_in.
generalize (rel_prime_is_inv p); case (rel_prime_dec p); auto.
apply mkZp_in; auto with zarith.
Qed.


Theorem phi_is_length: phi n = Z_of_nat (length Lrel).
assert (Hu: 0 < n); try apply Zlt_trans with 1; auto with zarith.
rewrite phi_def_with_0; auto.
unfold Zsum, Lrel; rewrite Zle_imp_le_bool; auto with zarith.
replace (1 + (n - 1) - 0) with n; auto with zarith.
elim (progression Zsucc 0 (Zabs_nat n)); simpl; auto.
intros a l1 Rec.
rewrite Rec.
rewrite rel_prime_is_inv.
case (rel_prime_dec a n); auto with zarith.
simpl length; rewrite inj_S; auto with zarith.
Qed.

Theorem phi_is_order: phi n = g_order ZPGroup.
unfold g_order; rewrite phi_is_length.
eq_tac; apply permutation_length.
apply ulist_incl2_permutation.
unfold Lrel; apply isupport_aux_ulist.
apply ulist_Zprogression; auto.
apply ZPGroup.(unique_s).
intros a H; unfold ZPGroup; simpl.
apply isupport_is_in.
unfold Lrel in H; apply  isupport_aux_is_inv_true with (1 := H).
apply mkZp_in; auto.
assert (In a (progression Zsucc 0 (Zabs_nat  n))).
apply  (isupport_aux_incl _ pmult mkZp 1 Z_eq_dec); auto.
split.
apply Zprogression_le_init with (1 := H0).
replace n with (0 + Z_of_nat (Zabs_nat n)).
apply Zprogression_le_end with (1 := H0).
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
intros a H; unfold Lrel; simpl.
apply isupport_aux_is_in.
simpl in H; apply  isupport_is_inv_true with (1 := H).
apply in_Zprogression.
rewrite Zplus_0_l; rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
assert (In a mkZp).
apply  (isupport_aux_incl _ pmult mkZp 1 Z_eq_dec); auto.
apply in_mkZp; auto.
Qed.

Theorem Zp_cyclic: prime n -> cyclic Z_eq_dec ZPGroup.
intros H1.
unfold ZPGroup, pmult;
generalize (cyclic_field _ (fun x y => (x + y) mod n) (fun x y => (x *  y) mod n) (fun x => (-x) mod n) 0);
unfold IA; intros tmp; apply tmp; clear tmp; auto.
intros; discriminate.
apply mkZp_in; auto with zarith.
intros; apply mkZp_in; auto with zarith.
apply Z_mod_lt; auto with zarith.
intros; rewrite Zplus_0_l; auto.
apply Zmod_small; auto.
apply in_mkZp; auto.
intros; rewrite Zplus_comm; auto.
intros a b c Ha Hb Hc.
pattern a at 1; rewrite <- (Zmod_small a n); auto with zarith.
pattern c at 2; rewrite <- (Zmod_small c n); auto with zarith.
repeat rewrite <- Zplus_mod; auto with zarith.
eq_tac; auto with zarith.
apply in_mkZp; auto.
apply in_mkZp; auto.
intros; eq_tac; auto with zarith.
intros a b c Ha Hb Hc.
pattern a at 1; rewrite <- (Zmod_small a n); auto with zarith.
repeat rewrite <- Zmult_mod; auto with zarith.
repeat rewrite <- Zplus_mod; auto with zarith.
eq_tac; auto with zarith.
apply in_mkZp; auto.
intros; apply mkZp_in; apply Z_mod_lt; auto with zarith.
intros a Ha.
pattern a at 1; rewrite <- (Zmod_small a n); auto with zarith.
repeat rewrite <- Zplus_mod; auto with zarith.
rewrite <- (Zmod_small 0 n); auto with zarith.
eq_tac; auto with zarith.
apply in_mkZp; auto.
intros a b Ha Hb H; case (prime_mult n H1 a b).
apply Zmod_divide; auto with zarith.
intros H2; left.
case (Zle_lt_or_eq 0 a); auto.
case (in_mkZp a); auto.
intros H3; absurd (n <= a).
apply Zlt_not_le.
case (in_mkZp a); auto.
apply Zdivide_le; auto with zarith.
intros H2; right.
case (Zle_lt_or_eq 0 b); auto.
case (in_mkZp b); auto.
intros H3; absurd (n <= b).
apply Zlt_not_le.
case (in_mkZp b); auto.
apply Zdivide_le; auto with zarith.
Qed.

End Zp.

(* Definition of the order (0 for q < 1) *)

Definition Zorder: Z -> Z -> Z.
intros p q; case (Z_le_dec q 1); intros H.
exact 0.
refine (e_order Z_eq_dec (p mod q) (ZPGroup q _)); auto with zarith.
Defined.

Theorem Zorder_pos: forall p n, 0 <= Zorder p n.
intros p n; unfold Zorder.
case (Z_le_dec n 1); auto with zarith.
intros n1.
apply Zlt_le_weak; apply e_order_pos.
Qed.

Theorem in_mod_ZPGroup
     : forall (n : Z) (n_pos : 1 < n) (p : Z),
       rel_prime p n -> In (p mod n) (s (ZPGroup n n_pos)).
intros n H p H1.
apply in_ZPGroup; auto.
apply rel_prime_mod; auto with zarith.
apply Z_mod_lt; auto with zarith.
Qed.


Theorem Zpower_mod_is_gpow:
  forall p q n (Hn: 1 < n), rel_prime p n -> 0 <= q -> p ^ q mod n = gpow (p mod n) (ZPGroup n Hn) q.
intros p q n H Hp H1; generalize H1; pattern q; apply natlike_ind; simpl; auto.
intros _; apply Zmod_small; auto with zarith.
intros n1 Hn1 Rec _; simpl.
generalize (in_mod_ZPGroup _ H _ Hp); intros Hu.
unfold Zsucc; rewrite Zpower_exp; try rewrite Zpower_1_r; auto with zarith.
rewrite gpow_add; auto with zarith.
rewrite gpow_1; auto; rewrite <- Rec; auto.
rewrite Zmult_mod; auto.
Qed.


Theorem Zorder_div_power: forall p q n, 1 < n -> rel_prime p n -> p ^ q  mod n = 1 -> (Zorder p n | q).
intros p q n H H1 H2.
assert (Hq: 0 <= q).
generalize H2; case q; simpl; auto with zarith.
intros p1 H3; contradict H3; rewrite Zmod_small; auto with zarith.
unfold Zorder; case (Z_le_dec n 1).
intros H3; contradict H; auto with zarith.
intros H3; apply e_order_divide_gpow; auto.
apply in_mod_ZPGroup; auto.
rewrite <- Zpower_mod_is_gpow; auto with zarith.
Qed.

Theorem Zorder_div:  forall p n,  prime n -> ~(n | p) -> (Zorder p n | n - 1).
intros p n H; unfold Zorder.
case (Z_le_dec n 1); intros H1 H2.
contradict H1; generalize (prime_ge_2 n H); auto with zarith.
rewrite <- prime_phi_n_minus_1; auto.
match goal with |- context[ZPGroup _ ?H2] => rewrite phi_is_order with (n_pos := H2) end.
apply e_order_divide_g_order; auto.
apply in_mod_ZPGroup; auto.
apply rel_prime_sym; apply prime_rel_prime; auto.
Qed.


Theorem Zorder_power_is_1:  forall p n, 1 < n -> rel_prime p n -> p ^ (Zorder p n)  mod n = 1.
intros p n H H1;  unfold Zorder.
case (Z_le_dec n 1); intros H2.
contradict H; auto with zarith.
let x := match goal with |- context[ZPGroup _ ?X] => X end  in  rewrite Zpower_mod_is_gpow with (Hn := x); auto with zarith.
rewrite gpow_e_order_is_e.
reflexivity.
apply in_mod_ZPGroup; auto.
apply Zlt_le_weak; apply e_order_pos.
Qed.

Theorem Zorder_power_pos: forall p n, 1 < n -> rel_prime p n -> 0 < Zorder p n.
intros p n H H1;  unfold Zorder.
case (Z_le_dec n 1); intros H2.
contradict H; auto with zarith.
apply e_order_pos.
Qed.

Theorem phi_power_is_1:  forall p n, 1 < n -> rel_prime p n -> p ^ (phi n)  mod n = 1.
intros p n H H1.
assert (V1:= Zorder_power_pos p n H H1).
assert (H2: (Zorder p n | phi n)).
unfold Zorder.
case (Z_le_dec n 1); intros H2.
contradict H; auto with zarith.
match goal with |- context[ZPGroup n ?H] =>
rewrite phi_is_order  with (n_pos := H)
end.
apply e_order_divide_g_order.
apply in_mod_ZPGroup; auto.
case H2; clear H2; intros q H2; rewrite H2.
rewrite Zmult_comm.
assert (V2 := (phi_pos _ H)).
assert (V3: 0 <= q).
rewrite H2 in V2.
apply Zlt_le_weak; apply Zmult_lt_0_reg_r with (2 := V2); auto with zarith.
rewrite Zpower_mult; auto with zarith.
rewrite Zpower_mod; auto with zarith.
rewrite Zorder_power_is_1; auto.
rewrite Zpower_1_l; auto with zarith.
apply Zmod_small; auto with zarith.
Qed.
