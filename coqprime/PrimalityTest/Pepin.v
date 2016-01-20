
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
    Pepin.v                        
                                                                     
    Pepin's Test for Fermat Number 
                                                                 
    Definition: PepinTest              
  **********************************************************************)
Require Import ZArith.
Require Import ZCAux.
Require Import Pocklington.

Open Scope Z_scope.

Definition FermatNumber n := 2^(2^(Z_of_nat n)) + 1.

Theorem Fermat_pos: forall n, 1 < FermatNumber n.
unfold FermatNumber; intros n; apply Zle_lt_trans with (2 ^ 2 ^(Z_of_nat n)); auto with zarith.
rewrite <- (Zpower_0_r 2); auto with zarith.
apply Zpower_le_monotone; try split; auto with zarith.
Qed.

Theorem PepinTest: forall n, let Fn := FermatNumber n in (3 ^ ((Fn - 1) / 2) + 1) mod Fn = 0 -> prime Fn.
intros n Fn H.
assert (Hn: 1 < Fn).
unfold Fn; apply Fermat_pos.
apply PocklingtonCorollary1 with (F1 := 2^(2^(Z_of_nat n))) (R1 := 1); auto with zarith.
2: unfold Fn, FermatNumber; auto with zarith.
apply Zlt_le_trans with (2 ^ 1); auto with zarith.
rewrite Zpower_1_r; auto with zarith.
apply Zpower_le_monotone; try split; auto with zarith.
rewrite <- (Zpower_0_r 2); apply Zpower_le_monotone; try split; auto with zarith.
unfold Fn, FermatNumber.
assert (H1: 2 <= 2 ^ 2 ^ Z_of_nat n).
pattern 2 at 1; rewrite <- (Zpower_1_r 2); auto with zarith.
apply Zpower_le_monotone; split; auto with zarith.
rewrite <- (Zpower_0_r 2); apply Zpower_le_monotone; try split; auto with zarith.
apply Zlt_le_trans with  (2 * 2 ^2 ^Z_of_nat n).
assert (tmp: forall p, 2 * p = p + p); auto with zarith.
apply Zmult_le_compat_r; auto with zarith.
assert (Hd: (2 | Fn - 1)).
exists (2 ^ (2^(Z_of_nat n) - 1)).
pattern 2 at 3; rewrite <- (Zpower_1_r 2).
rewrite <- Zpower_exp; auto with zarith.
assert (tmp: forall p, p = (p - 1) +1); auto with zarith; rewrite <- tmp.
unfold Fn, FermatNumber; ring.
assert (0 < 2 ^ Z_of_nat n); auto with zarith.
intros p Hp Hp1; exists 3; split; auto with zarith; split; auto.
rewrite (Zdivide_Zdiv_eq  2 (Fn -1)); auto with zarith.
rewrite Zmult_comm; rewrite Zpower_mult; auto with zarith.
rewrite Zpower_mod; auto with zarith.
assert (tmp: forall p, p = (p + 1) -1); auto with zarith; rewrite (fun x => (tmp (3 ^ x))).
rewrite Zminus_mod; auto with zarith.
rewrite H.
rewrite (Zmod_small 1); auto with zarith.
rewrite <- Zpower_mod; auto with zarith.
rewrite Zmod_small; auto with zarith.
simpl; unfold Zpower_pos; simpl; auto with zarith.
apply Z_div_pos; auto with zarith.
apply Zis_gcd_gcd; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
intros x HD1 HD2.
assert (Hd1: p = 2).
apply prime_div_Zpower_prime with (4 := Hp1); auto with zarith.
apply prime_2.
assert (Hd2: (x | 2)).
replace 2 with ((3 ^ ((Fn - 1) / 2) + 1) - (3 ^ ((Fn - 1) / 2) - 1)); auto with zarith.
apply Zdivide_minus_l; auto.
apply Zdivide_trans with (1 := HD2).
apply Zmod_divide; auto with zarith.
rewrite <- Hd1; auto.
replace 1 with (Fn - (Fn - 1)); auto with zarith.
apply Zdivide_minus_l; auto.
apply Zdivide_trans with (1 := Hd2); auto.
Qed.

(* An optimized version with Zpow_mod *)

Definition pepin_test n :=
  let Fn := FermatNumber n in if  Z_eq_dec (Zpow_mod 3  ((Fn - 1) / 2) Fn)  (Fn - 1) then true else false.

Theorem PepinTestOp: forall n, pepin_test n = true -> prime (FermatNumber n).
intros n; unfold pepin_test.
match goal with |- context[if ?X then _ else _] => case X end; try (intros; discriminate).
intros H1 _; apply PepinTest.
generalize (Fermat_pos n); intros H2.
rewrite Zplus_mod; auto with zarith.
rewrite <- Zpow_mod_Zpower_correct; auto with zarith.
rewrite H1.
rewrite (Zmod_small 1); auto with zarith.
replace (FermatNumber n - 1 + 1) with (FermatNumber n); auto with zarith.
apply Zdivide_mod; auto with zarith.
apply Z_div_pos; auto with zarith.
Qed.

Theorem prime5: prime 5.
exact (PepinTestOp 1 (refl_equal _)).
Qed.

Theorem prime17: prime 17.
exact (PepinTestOp 2 (refl_equal _)).
Qed.

Theorem prime257:  prime 257.
exact (PepinTestOp 3 (refl_equal _)).
Qed.

Theorem prime65537:  prime 65537.
exact (PepinTestOp 4 (refl_equal _)).
Qed.

(* Too tough !! 
Theorem prime4294967297:  prime 4294967297.
refine (PepinTestOp 5 (refl_equal _)).
Qed.
*)
