Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Specific.MontgomeryP256_128.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.DestructHead.
Import ListNotations.

Require Import Crypto.Specific.Framework.IntegrationTestTemporaryMiscCommon.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let bounds : Tuple.tuple zrange sz
    := Eval compute in
        Tuple.repeat {| lower := 0 ; upper := r-1 |} sz.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (Z.log2_up r))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let eval : feBW -> Z :=
    fun x => MontgomeryAPI.eval (Z.pos r) (BoundedWordToZ _ _ _ x).
  Let feBW_small : Type := { v : feBW | eval v < MontgomeryAPI.eval (n:=sz) (Z.pos r) p256 }.
  Let feBW_of_feBW_small : feBW_small -> feBW := @proj1_sig _ _.
  Local Coercion feBW_of_feBW_small : feBW_small >-> feBW.
  Let phi : feBW -> F m :=
    fun x => montgomery_to_F (eval x).

  Local Ltac op_sig_side_conditions_t _ :=
    try (hnf; rewrite <- (is_bounded_by_None_repeat_In_iff_lt _ _ _)); destruct_head_hnf' sig; try assumption.

  (* TODO : change this to field once field isomorphism happens *)
  Definition opp
    : { opp : feBW_small -> feBW_small
      | forall A, phi (opp A) = F.opp (phi A) }.
  Proof.
    start_preglue.
    all:cbv [feBW_of_feBW_small eval].
    do_rewrite_with_sig_by opp op_sig_side_conditions_t.
    cbv_runtime.
    all:fin_preglue.
    factor_out_bounds_and_strip_eval opp_bounded op_sig_side_conditions_t.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*     Set Ltac Profiling.
    Print Ltac ReflectiveTactics.solve_side_conditions.
    Ltac ReflectiveTactics.solve_side_conditions ::= idtac.
    Time refine_reflectively128_with_uint8_with anf. (* Finished transaction in 212.693 secs (212.576u,0.184s) (successful) *)
    { Time ReflectiveTactics.do_reify. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Require Import CNotations.
      Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
  { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
  { Time SubstLet.subst_let; clear; abstract vm_cast_no_check eq_refl. }
  { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
  { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
  { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }
  { Time ReflectiveTactics.handle_boundedness_side_condition. } *)
    Time refine_reflectively128_with_uint8_with anf. (* Finished transaction in 212.693 secs (212.576u,0.184s) (successful) *)
    Show Ltac Profile.
    (* total time:     19.632s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
─ReflectiveTactics.do_reflective_pipelin  -0.0%  96.2%       1   18.884s
─ReflectiveTactics.solve_side_conditions   1.2%  96.1%       1   18.860s
─ReflectiveTactics.do_reify ------------  27.7%  44.0%       1    8.640s
─ReflectiveTactics.abstract_vm_compute_r  12.3%  13.9%       2    2.024s
─ReflectiveTactics.abstract_vm_compute_r   8.9%  12.2%       2    1.576s
─Reify_rhs_gen -------------------------   0.8%  11.7%       1    2.300s
─ReflectiveTactics.renamify_rhs --------  10.4%  11.5%       1    2.260s
─ReflectiveTactics.abstract_rhs --------   4.6%   5.8%       1    1.148s
─clear (var_list) ----------------------   5.2%   5.2%      57    0.184s
─eexact --------------------------------   4.1%   4.1%      68    0.028s
─prove_interp_compile_correct ----------   0.0%   3.4%       1    0.664s
─ReflectiveTactics.abstract_cbv_interp_r   2.7%   3.3%       1    0.648s
─unify (constr) (constr) ---------------   3.2%   3.2%       6    0.248s
─rewrite ?EtaInterp.InterpExprEta ------   3.1%   3.1%       1    0.612s
─ReflectiveTactics.abstract_cbv_rhs ----   2.0%   2.7%       1    0.532s
─Glue.refine_to_reflective_glue --------   0.0%   2.2%       1    0.436s
─rewrite H -----------------------------   2.1%   2.1%       1    0.420s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
 ├─ReflectiveTactics.do_reflective_pipel  -0.0%  96.2%       1   18.884s
 │└ReflectiveTactics.solve_side_conditio   1.2%  96.1%       1   18.860s
 │ ├─ReflectiveTactics.do_reify --------  27.7%  44.0%       1    8.640s
 │ │ ├─Reify_rhs_gen -------------------   0.8%  11.7%       1    2.300s
 │ │ │ ├─prove_interp_compile_correct --   0.0%   3.4%       1    0.664s
 │ │ │ │└rewrite ?EtaInterp.InterpExprEt   3.1%   3.1%       1    0.612s
 │ │ │ └─rewrite H ---------------------   2.1%   2.1%       1    0.420s
 │ │ └─eexact --------------------------   4.1%   4.1%      68    0.028s
 │ ├─ReflectiveTactics.abstract_vm_compu  12.3%  13.9%       2    2.024s
 │ ├─ReflectiveTactics.abstract_vm_compu   8.9%  12.2%       2    1.576s
 │ ├─ReflectiveTactics.renamify_rhs ----  10.4%  11.5%       1    2.260s
 │ ├─ReflectiveTactics.abstract_rhs ----   4.6%   5.8%       1    1.148s
 │ ├─ReflectiveTactics.abstract_cbv_inte   2.7%   3.3%       1    0.648s
 │ └─ReflectiveTactics.abstract_cbv_rhs    2.0%   2.7%       1    0.532s
 └─Glue.refine_to_reflective_glue ------   0.0%   2.2%       1    0.436s
*)
  Time Defined. (* Finished transaction in 21.291 secs (21.231u,0.032s) (successful) *)

Time End BoundedField25p5. (* Finished transaction in 14.666 secs (14.556u,0.111s) (successful) *)

Print Assumptions opp.
