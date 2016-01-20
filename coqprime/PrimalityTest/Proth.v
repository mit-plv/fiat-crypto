
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    Proth.v                        
                                                                     
    Proth's Test 
                                                                 
    Definition: ProthTest              
 **********************************************************************)
Require Import ZArith.
Require Import ZCAux.
Require Import Pocklington.

Open Scope Z_scope.

Theorem ProthTest: forall h k a, let n := h * 2 ^ k + 1 in 1 < a -> 0 < h < 2 ^k -> (a ^ ((n - 1) / 2) + 1) mod n = 0 -> prime n.
intros h k a n; unfold n; intros H H1 H2.
assert (Hu: 0 < h * 2 ^ k).
apply Zmult_lt_O_compat; auto with zarith.
assert (Hu1: 0 < k).
case (Zle_or_lt k 0); intros Hv; auto.
generalize H1 Hv; case k; simpl.
intros (Hv1, Hv2); contradict Hv2; auto with zarith.
intros p1 _ Hv1; contradict Hv1; auto with zarith.
intros   p (Hv1, Hv2); contradict Hv2; auto with zarith.
apply PocklingtonCorollary1 with (F1 := 2 ^ k) (R1 := h); auto with zarith.
ring.
apply Zlt_le_trans with ((h + 1) * 2 ^ k); auto with zarith.
rewrite Zmult_plus_distr_l; apply Zplus_lt_compat_l.
rewrite Zmult_1_l; apply Zlt_le_trans with 2; auto with zarith.
intros p H3 H4.
generalize H2; replace (h * 2 ^ k + 1 - 1) with (h * 2 ^k); auto with zarith; clear H2; intros H2.
exists a; split; auto; split.
pattern (h * 2 ^k) at 1; rewrite (Zdivide_Zdiv_eq  2 (h * 2 ^ k)); auto with zarith.
rewrite (Zmult_comm 2); rewrite Zpower_mult; auto with zarith.
rewrite Zpower_mod; auto with zarith.
assert (tmp: forall p, p = (p + 1) -1); auto with zarith; rewrite (fun x => (tmp (a ^ x))).
rewrite Zminus_mod; auto with zarith.
rewrite H2.
rewrite (Zmod_small 1); auto with zarith.
rewrite <- Zpower_mod; auto with zarith.
rewrite Zmod_small; auto with zarith.
simpl; unfold Zpower_pos; simpl; auto with zarith.
apply Z_div_pos; auto with zarith.
apply Zdivide_trans with (2 ^ k).
apply Zpower_divide; auto with zarith.
apply Zdivide_factor_l; auto with zarith.
apply Zis_gcd_gcd; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
intros x HD1 HD2.
assert (Hd1: p = 2).
apply prime_div_Zpower_prime with (4 := H4); auto with zarith.
apply prime_2.
assert (Hd2: (x | 2)).
replace 2 with ((a ^ (h * 2 ^ k / 2) + 1) - (a ^ (h * 2 ^ k/ 2) - 1)); auto with zarith.
apply Zdivide_minus_l; auto.
apply Zdivide_trans with (1 := HD2).
apply Zmod_divide; auto with zarith.
pattern 2 at 2; rewrite <- Hd1; auto.
replace 1 with ((h * 2 ^k + 1) - (h * 2 ^ k)); auto with zarith.
apply Zdivide_minus_l; auto.
apply Zdivide_trans with (1 := Hd2); auto.
apply Zdivide_trans with (2 ^ k).
apply Zpower_divide; auto with zarith.
apply Zdivide_factor_l; auto with zarith.
Qed.


Definition proth_test h k a :=
  let n := h * 2 ^ k + 1 in 
   if (Z_lt_dec 1  a) then 
      if (Z_lt_dec 0 h) then
        if (Z_lt_dec h (2 ^k)) then
            if Z_eq_dec (Zpow_mod a  ((n - 1) / 2) n) (n - 1) then true
            else false else false else false else false. 

 
Theorem ProthTestOp: forall h k a, proth_test h k a = true -> prime (h * 2 ^ k + 1).
intros h k a; unfold proth_test.
repeat match goal with |- context[if ?X then _ else _] => case X end; try (intros; discriminate).
intros H1 H2 H3 H4 _.
assert (Hu: 0 < h * 2 ^ k).
apply Zmult_lt_O_compat; auto with zarith.
apply ProthTest with (a := a); auto.
rewrite Zplus_mod; auto with zarith.
rewrite <- Zpow_mod_Zpower_correct; auto with zarith.
rewrite H1.
rewrite (Zmod_small 1); auto with zarith.
replace (h * 2 ^ k + 1 - 1 + 1) with (h * 2 ^ k + 1); auto with zarith.
apply Zdivide_mod; auto with zarith.
apply Z_div_pos; auto with zarith.
Qed.

Theorem prime5: prime 5.
exact (ProthTestOp 1 2 2 (refl_equal _)).
Qed.

Theorem prime17: prime 17.
exact (ProthTestOp 1 4 3 (refl_equal _)).
Qed.

Theorem prime257:  prime 257.
exact (ProthTestOp 1 8 3 (refl_equal _)).
Qed.

Theorem prime65537:  prime 65537.
exact (ProthTestOp 1 16 3 (refl_equal _)).
Qed.

(* Too tough !! 
Theorem prime4294967297:  prime 4294967297.
exact (ProthTestOp 1 32 3 (refl_equal _)).
Qed.
*)
