Require Import Coq.ZArith.ZArith.
Require Export Crypto.Util.ZUtil.Hints.Core.

Hint Resolve Z.log2_nonneg Z.log2_up_nonneg Z.div_small Z.mod_small Z.pow_neg_r Z.pow_0_l Z.pow_pos_nonneg Z.lt_le_incl Z.pow_nonzero Z.div_le_upper_bound Z_div_exact_full_2 Z.div_same Z.div_lt_upper_bound Z.div_le_lower_bound Zplus_minus Zplus_gt_compat_l Zplus_gt_compat_r Zmult_gt_compat_l Zmult_gt_compat_r Z.pow_lt_mono_r Z.pow_lt_mono_l Z.pow_lt_mono Z.mul_lt_mono_nonneg Z.div_lt_upper_bound Z.div_pos Zmult_lt_compat_r Z.pow_le_mono_r Z.pow_le_mono_l Z.div_lt Z.div_le_compat_l Z.div_le_mono Z.max_le_compat Z.min_le_compat Z.log2_up_le_mono Z.pow_nonneg : zarith.
Hint Resolve (fun a b H => proj1 (Z.mod_pos_bound a b H)) (fun a b H => proj2 (Z.mod_pos_bound a b H)) (fun a b pf => proj1 (Z.pow_gt_1 a b pf)) : zarith.
Hint Resolve (fun n m => proj1 (Z.opp_le_mono n m)) : zarith.
Hint Resolve (fun n m => proj1 (Z.pred_le_mono n m)) : zarith.
Hint Resolve (fun a b => proj2 (Z.lor_nonneg a b)) : zarith.
