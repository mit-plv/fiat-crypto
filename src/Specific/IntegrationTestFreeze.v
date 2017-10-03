Require Import Crypto.Specific.X25519.C64.ReificationTypes.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.

(* TODO : change this to field once field isomorphism happens *)
Definition freeze :
  { freeze : feBW -> feBW
  | forall a, phiBW (freeze a) = phiBW a }.
Proof.
  start_preglue.
  do_rewrite_with_sig_by freeze_sig ltac:(fun _ => apply feBW_bounded); cbv_runtime.
  all:fin_preglue.
  (* jgross start here! *)
  (*Set Ltac Profiling.*)
  Time refine_reflectively_gen P.freeze_allowable_bit_widths anf. (* Finished transaction in 5.792 secs (5.792u,0.004s) (successful) *)
  (*Show Ltac Profile.*)
  (* total time:      5.680s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively_gen ---------------   0.0% 100.0%       1    5.680s
─ReflectiveTactics.do_reflective_pipelin   0.0%  95.8%       1    5.444s
─ReflectiveTactics.solve_side_conditions   0.4%  95.6%       1    5.428s
─ReflectiveTactics.do_reify ------------  46.0%  61.7%       1    3.504s
─UnifyAbstractReflexivity.unify_transfor  22.9%  28.4%       7    0.372s
─Reify_rhs_gen -------------------------   0.7%   8.3%       1    0.472s
─eexact --------------------------------   7.2%   7.2%     131    0.012s
─ReflectiveTactics.unify_abstract_cbv_in   3.9%   4.9%       1    0.280s
─Glue.refine_to_reflective_glue' -------   0.0%   4.2%       1    0.236s
─Glue.zrange_to_reflective -------------   0.1%   3.3%       1    0.188s
─unify (constr) (constr) ---------------   3.2%   3.2%       6    0.052s
─prove_interp_compile_correct ----------   0.0%   2.7%       1    0.152s
─clear (var_list) ----------------------   2.7%   2.7%      91    0.028s
─rewrite ?EtaInterp.InterpExprEta ------   2.5%   2.5%       1    0.140s
─ClearAll.clear_all --------------------   0.4%   2.5%       7    0.036s
─Glue.zrange_to_reflective_goal --------   2.0%   2.4%       1    0.136s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively_gen ---------------   0.0% 100.0%       1    5.680s
 ├─ReflectiveTactics.do_reflective_pipel   0.0%  95.8%       1    5.444s
 │└ReflectiveTactics.solve_side_conditio   0.4%  95.6%       1    5.428s
 │ ├─ReflectiveTactics.do_reify --------  46.0%  61.7%       1    3.504s
 │ │ ├─Reify_rhs_gen -------------------   0.7%   8.3%       1    0.472s
 │ │ │└prove_interp_compile_correct ----   0.0%   2.7%       1    0.152s
 │ │ │└rewrite ?EtaInterp.InterpExprEta    2.5%   2.5%       1    0.140s
 │ │ └─eexact --------------------------   7.2%   7.2%     131    0.012s
 │ ├─UnifyAbstractReflexivity.unify_tran  22.9%  28.4%       7    0.372s
 │ │ ├─ClearAll.clear_all --------------   0.4%   2.5%       7    0.036s
 │ │ │└clear (var_list) ----------------   2.1%   2.1%      70    0.028s
 │ │ └─unify (constr) (constr) ---------   2.3%   2.3%       5    0.044s
 │ └─ReflectiveTactics.unify_abstract_cb   3.9%   4.9%       1    0.280s
 └─Glue.refine_to_reflective_glue' -----   0.0%   4.2%       1    0.236s
  └Glue.zrange_to_reflective -----------   0.1%   3.3%       1    0.188s
  └Glue.zrange_to_reflective_goal ------   2.0%   2.4%       1    0.136s

   *)
Time Defined. (* Finished transaction in 3.607 secs (3.607u,0.s) (successful) *)
