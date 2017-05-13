Require Import Coq.ZArith.ZArith.
Require Export Crypto.Util.ZUtil.Hints.Core.

Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l Z.sub_diag Zdiv_0_r : zsimplify_fast.

Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l Zplus_minus Z.add_diag Z.abs_0 Z.sgn_0 Nat2Z.inj_0 Z2Nat.inj_0 Zdiv_0_r : zsimplify.
Hint Rewrite Z.div_mul Z.div_1_l Z.div_same Z.mod_same Z.div_small Z.mod_small Z.div_add Z.div_add_l Z.mod_add Z.div_0_l Z.mod_mod Z.mod_small Z_mod_zero_opp_full Z.mod_1_l using zutil_arith : zsimplify.
Hint Rewrite <- Z.opp_eq_mul_m1 Z.one_succ Z.two_succ : zsimplify.
Hint Rewrite <- Z.div_mod using zutil_arith : zsimplify.
Hint Rewrite (fun x y => proj2 (Z.eqb_neq x y)) using assumption : zsimplify.
Hint Rewrite Z.mul_0_l Z.mul_0_r Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r Z.sub_0_l Z.sub_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_0_l Zmod_0_r Zmod_1_r Z.opp_0 Z.abs_0 Z.sgn_0 Nat2Z.inj_0 Z2Nat.inj_0 : zsimplify_const.

Hint Rewrite <- Z.one_succ Z.two_succ : zsimplify_const.

Hint Rewrite Nat2Z.id N2Z.id : zsimplify.
