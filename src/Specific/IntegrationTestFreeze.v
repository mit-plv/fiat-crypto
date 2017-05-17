Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.DestructHead.
Import ListNotations.

Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (* TODO : change this to field once field isomorphism happens *)
  Definition freeze :
    { freeze : feBW -> feBW
    | forall a, phi (freeze a) = phi a }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a, ?phi (f a) = @?rhs a } ]
      => apply lift1_sig with (P:=fun a f => phi f = rhs a)
    end.
    intros.
    eexists_sig_etransitivity. all:cbv [phi].
    rewrite <- (proj2_sig freeze_sig).
    { set (freezeZ := proj1_sig freeze_sig).
      context_to_dlet_in_rhs freezeZ.
      cbv beta iota delta [freezeZ proj1_sig freeze_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz].
      reflexivity. }
    { destruct a as [a H]; unfold BoundedWordToZ, proj1_sig.
      revert H.
      cbv -[Z.le Z.add Z.mul Z.lt fst snd wordToZ wt]; cbn [fst snd].
      repeat match goal with
             | [ |- context[wt ?n] ]
               => let v := (eval compute in (wt n)) in change (wt n) with v
             end.
      intro; destruct_head'_and.
      omega. }
    sig_dlet_in_rhs_to_context.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    (* jgross start here! *)
    (*Set Ltac Profiling.*)
    Time refine_reflectively. (* Finished transaction in 5.792 secs (5.792u,0.004s) (successful) *)
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

End BoundedField25p5.
