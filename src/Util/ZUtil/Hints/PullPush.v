Require Import Coq.ZArith.ZArith.
Require Export Crypto.Util.ZUtil.Hints.Core.

(** "push" means transform [-f x] to [f (-x)]; "pull" means go the other way *)
Hint Rewrite Z.div_opp_l_nz Z.div_opp_l_z using zutil_arith : pull_Zopp.
Hint Rewrite Z.mul_opp_l : pull_Zopp.
Hint Rewrite <- Z.opp_add_distr : pull_Zopp.
Hint Rewrite <- Z.div_opp_l_nz Z.div_opp_l_z using zutil_arith : push_Zopp.
Hint Rewrite <- Z.mul_opp_l : push_Zopp.
Hint Rewrite Z.opp_add_distr : push_Zopp.
Hint Rewrite Z.pow_sub_r Z.pow_div_l Z.pow_twice_r Z.pow_mul_l Z.pow_add_r using zutil_arith : push_Zpow.
Hint Rewrite <- Z.pow_sub_r Z.pow_div_l Z.pow_mul_l Z.pow_add_r Z.pow_twice_r using zutil_arith : pull_Zpow.
Hint Rewrite Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : push_Zmul.
Hint Rewrite <- Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : pull_Zmul.
Hint Rewrite Z.div_div using zutil_arith : pull_Zdiv.
Hint Rewrite <- Z.div_div using zutil_arith : push_Zdiv.
Hint Rewrite <- Z.mul_mod Z.add_mod Zminus_mod using zutil_arith : pull_Zmod.
Hint Rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r : pull_Zmod.
Hint Rewrite Z_mod_nz_opp_full using zutil_arith : push_Zmod.
Hint Rewrite Z_mod_same_full : push_Zmod.
Hint Rewrite Nat2Z.id : push_Zof_nat.
Hint Rewrite N2Z.id : push_Zto_N.
Hint Rewrite N2Z.id : pull_Zof_N.
Hint Rewrite N2Z.inj_pos N2Z.inj_abs_N N2Z.inj_add N2Z.inj_mul N2Z.inj_sub_max N2Z.inj_succ N2Z.inj_pred_max N2Z.inj_min N2Z.inj_max N2Z.inj_div N2Z.inj_quot N2Z.inj_rem N2Z.inj_div2 N2Z.inj_pow N2Z.inj_0 nat_N_Z : push_Zof_N.
Hint Rewrite N2Z.inj_compare N2Z.inj_testbit : pull_Zof_N.
Hint Rewrite <- N2Z.inj_abs_N N2Z.inj_add N2Z.inj_mul N2Z.inj_sub_max N2Z.inj_succ N2Z.inj_pred_max N2Z.inj_min N2Z.inj_max N2Z.inj_div N2Z.inj_quot N2Z.inj_rem N2Z.inj_div2 N2Z.inj_pow : pull_Zof_N.
Hint Rewrite Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : push_Zof_nat.
Hint Rewrite <- Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : pull_Zof_nat.
Hint Rewrite Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : pull_Zshift.
Hint Rewrite <- Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : pull_Zshift.
Hint Rewrite Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : push_Zshift.
Hint Rewrite <- Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : push_Zshift.
Hint Rewrite Z.shiftr_opp_r Z.shiftl_opp_r Z.shiftr_0_r Z.shiftr_0_l Z.shiftl_0_r Z.shiftl_0_l : push_Zshift.
Hint Rewrite Z.shiftl_1_l Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 Z.opp_involutive using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_opp_r using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : Zpow_to_shift.
Hint Rewrite Z.add_max_distr_r Z.add_max_distr_l : push_Zmax.
Hint Rewrite <- Z.add_max_distr_r Z.add_max_distr_l : pull_Zmax.
