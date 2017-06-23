Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Specific.NISTP256.AMD64.MontgomeryP256.
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

  Let bounds : Tuple.tuple zrange sz
    := Eval compute in
        Tuple.repeat {| lower := 0 ; upper := r-1 |} sz.

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (Z.log2_up r))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let eval : feBW -> Z :=
    fun x => Saturated.eval (Z.pos r) (BoundedWordToZ _ _ _ x).
  Let feBW_small : Type := { v : feBW | eval v < Saturated.eval (n:=sz) (Z.pos r) p256 }.
  Let feBW_of_feBW_small : feBW_small -> feBW := @proj1_sig _ _.
  Local Coercion feBW_of_feBW_small : feBW_small >-> feBW.
  Let phi : feBW -> F m :=
    fun x => montgomery_to_F (eval x).

  Axiom proof_admitted : False.

  (* TODO : change this to field once field isomorphism happens *)
  Definition opp
    : { opp : feBW_small -> feBW_small
      | forall A, phi (opp A) = F.opp (phi A) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a, ?phi (?proj (f a)) = @?rhs a } ]
      => apply lift1_sig with (P:=fun a f => phi (proj f) = rhs a)
    end.
    intros a.
    cbv [feBW_of_feBW_small].
    eexists_sig_etransitivity. all:cbv [phi eval].
    rewrite <- (proj1 (proj2_sig opp))
      by (try (hnf; rewrite <- (is_bounded_by_None_repeat_In_iff_lt _ _ _)); destruct_head' feBW_small; destruct_head' feBW; try assumption).
    reflexivity.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    Associativity.sig_sig_assoc.
    apply sig_conj_by_impl2.
    { intros ? H; cbv [eval]; rewrite H; clear H.
      apply (proj2 (proj2_sig opp)); destruct_head' feBW_small; try assumption;
        hnf; rewrite <- (is_bounded_by_None_repeat_In_iff_lt _ _ _); destruct_head' feBW; assumption. }
    eexists_sig_etransitivity.
    set (oppZ := proj1_sig opp).
    context_to_dlet_in_rhs oppZ; cbv [oppZ].
    cbv beta iota delta [opp opp' proj1_sig Saturated.T lift2_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr].
    reflexivity.
    sig_dlet_in_rhs_to_context.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    match goal with
    | [ H : feBW_small |- _ ] => destruct H as [? _]
    end.
    (* jgross start here! *)
    Set Ltac Profiling.
    (*     Set Ltac Profiling.
    Print Ltac ReflectiveTactics.solve_side_conditions.
    Ltac ReflectiveTactics.solve_side_conditions ::= idtac.
    Time refine_reflectively_with_uint8_with anf. (* Finished transaction in 212.693 secs (212.576u,0.184s) (successful) *)
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
    Time repeat unshelve esplit; abstract case proof_admitted; refine_reflectively_with_uint8_with anf. (* Finished transaction in 212.693 secs (212.576u,0.184s) (successful) *)
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
