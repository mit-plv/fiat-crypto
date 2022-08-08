Require Import Coq.ZArith.ZArith.
Require Export Crypto.Util.ZUtil.Hints.Core.

#[global]
Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : convert_to_Ztestbit.

#[global]
Hint Rewrite Z.testbit_0_l Z.land_spec Z.lor_spec : Ztestbit.
#[global]
Hint Rewrite Z.testbit_0_l Z.land_spec Z.lor_spec : Ztestbit_full.
#[global]
Hint Rewrite Z.shiftl_spec Z.shiftr_spec using zutil_arith : Ztestbit.
#[global]
Hint Rewrite Z.testbit_neg_r using zutil_arith : Ztestbit.
#[global]
Hint Rewrite Bool.andb_true_r Bool.andb_false_r Bool.orb_true_r Bool.orb_false_r
             Bool.andb_true_l Bool.andb_false_l Bool.orb_true_l Bool.orb_false_l : Ztestbit.
