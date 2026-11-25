Set Loose Hint Behavior "Strict".
Require Import Coq.ZArith.ZArith.
Require Import bbv.ZLib.

(* Properties of the lemmas in this list:
   - they are equalities about Z where the rhs is a simplification of the lhs
   - they have no preconditions
   - there should be no reason you would not want to rewrite with them *)
Hint Rewrite
     Z.land_diag
     Z.lor_diag
     Z.min_id
     Z.max_id
     Z.opp_involutive
     Z.lnot_involutive
     Z.ldiff_diag
     Z.ldiff_0_r
     Z.lxor_0_l
     Z.lxor_nilpotent
     Z.land_0_r
     Z.lor_0_r
     Z.sgn_sgn
     Zdiv_0_r
     Z.ldiff_0_l
     Z.shiftl_0_r
     Z.shiftr_0_l
     Z.shiftl_0_l
     Z.shiftr_0_r
     Z.land_0_l
     Zmod_0_r
     Z.lcm_0_r
     Z.lcm_0_l
     Z.lor_0_l
     Z.add_0_l
     Z.lxor_0_r
     Z.mul_0_r
     Z_mod_same_full
     Z.sub_0_r
     Z.sub_diag
     Z.abs_involutive
     Z.mul_0_l
     Zmod_0_l
     Z.add_0_r
     Zdiv_0_l
     Z.succ_pred
     Z.pred_succ
     Z.abs_opp
     Z.sub_0_l
     Z.div_1_r
     Z.land_lnot_diag
     Z.mul_1_r
     Z.add_opp_diag_r
     Z.pow_1_r
     Z.min_max_absorption
     Z.max_min_absorption
     Z.quot_1_r
     Z.add_opp_diag_l
     Z.mul_1_l
     Zmod_mod
     Z.rem_opp_r'
     Z.rem_1_r
     Z_mod_mult'
     Zmod_1_r
     Z.pow_0_r
     Z_mod_mult
     Z.land_ldiff
     Z.mod_1_r
     Z.lxor_lnot_lnot
     Z.land_m1_l
     Z.land_m1_r
     Z.shiftl_opp_r
     Z.shiftr_opp_r
: rew_Z_trivial.
