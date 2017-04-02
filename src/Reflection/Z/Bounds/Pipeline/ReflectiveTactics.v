(** * Reflective Pipeline: Tactics that execute the pipeline *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.RenameBinders.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.Z.Bounds.Relax.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.OutputType.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstLet.
Require Import Crypto.Util.Option.

Module Export Exports.
  Export Crypto.Reflection.Reify. (* export for the instances for recursing under binders *)
  Export Crypto.Reflection.Z.Reify. (* export for the tactic redefinitions *)
End Exports.

Ltac rexpr_cbv :=
  lazymatch goal with
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?uncurry ?oper x } ]
    => let operf := head oper in
       let uncurryf := head uncurry in
       try cbv delta [T]; try cbv delta [oper];
       try cbv beta iota delta [uncurryf]
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?oper x } ]
    => let operf := head oper in
       try cbv delta [T]; try cbv delta [oper]
  end;
  cbv beta iota delta [interp_flat_type interp_base_type].
Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.
Ltac assert_reflective :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds _
         /\ cast_back_flat_const ?fW = ?fZ (cast_back_flat_const ?v) ]
    => let rexpr := fresh "rexpr" in
       simple refine (let rexpr : { rexpr | forall x, Interp interp_op (t:=T) rexpr x = fZ x } := _ in _);
       [ cbv [interp_flat_type interp_base_type Tuple.tuple Tuple.tuple'] in *;
         subst fW
       | rewrite <- (proj2_sig rexpr);
         let rexpr' := fresh rexpr in
         set (rexpr' := proj1_sig rexpr);
         unfold proj1_sig in rexpr';
         subst rexpr fZ ]
  end.
Ltac prove_rexpr_wfT
  := reflect_Wf Equality.base_type_eq_semidec_is_dec Equality.op_beq_bl.

Ltac assert_wf :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds _
         /\ cast_back_flat_const ?fW = Interp _ ?fZ (@cast_back_flat_const _ _ _ ?input_bounds ?v) ]
    => assert (Wf fZ) by (clear; prove_rexpr_wfT)
  end.

Notation rexpr_post_wf_pipeline_option rexprZ rexpr_bounds
  := (PostWfPipeline rexprZ rexpr_bounds)
       (only parsing).
Notation rexpr_post_wf_pipeline_postprocess1 v
  := (invert_Some v)
       (only parsing).
Notation get_output_type v := (OutputType v) (only parsing).
Notation get_bounds v := (@output_bounds v) (only parsing).
Notation get_output_expr v := (@output_expr v) (only parsing).
Notation rexpr_post_wf_pipeline_postprocess2 v
  := (renamify v)
       (only parsing).

Notation rexpr_correct_and_bounded rexprZ rexprW input_bounds output_bounds rexprZ_Wf
  := (fun v v' Hv
      => proj2
           (@PostWfPipelineCorrct
              _ rexprZ input_bounds rexprZ_Wf
              output_bounds rexprW
              _
              v v' Hv))
       (only parsing).

Ltac rexpr_correct_and_bounded_obligation_tac :=
  intros; subst_let; clear;
  lazymatch goal with
  | [ |- ?x = Some ?y ]
    => abstract vm_cast_no_check (eq_refl (Some y))
  | _ => vm_compute; constructor
  end.


Ltac make_correctness rexprZ bounds Hcorrectness :=
  let rexprW_pkgo := (eval vm_compute in (rexpr_post_wf_pipeline_option rexprZ bounds)) in
  let rexprW_pkg := (eval vm_compute in (rexpr_post_wf_pipeline_postprocess1 rexprW_pkgo)) in
  let rexprT := constr:(get_output_type rexprW_pkg) in
  let rexprW' := (eval vm_compute in (get_output_expr rexprW_pkg)) in
  let rexprW := (eval cbv beta iota zeta in (rexpr_post_wf_pipeline_postprocess2 rexprW')) in
  let rexpr_output_bounds := (eval vm_compute in (get_bounds rexprW_pkg)) in
  let rexprZ_Wf := lazymatch goal with H : Wf rexprZ |- _ => H end in
  simple refine (let Hcorrectness := rexpr_correct_and_bounded rexprZ rexprW bounds rexpr_output_bounds rexprZ_Wf in _);
  [ rexpr_correct_and_bounded_obligation_tac.. | clearbody Hcorrectness ].
Ltac do_pose_correctness Hcorrectness :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds _
         /\ cast_back_flat_const ?fW = Interp _ ?fZ (@cast_back_flat_const _ _ _ ?input_bounds ?v) ]
    => make_correctness fZ input_bounds Hcorrectness
  end.
Ltac pretighten_bounds tighter_bounds :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by ?t ?relaxed_bounds _ /\ cast_back_flat_const ?v = ?k ]
    => simple refine (@relax_output_bounds t tighter_bounds relaxed_bounds _ v k _ _)
  end.
Ltac posttighten_bounds :=
  [ > clear; vm_compute; reflexivity | unfold eq_rect | clear; abstract vm_cast_no_check (eq_refl true) ].
Ltac pretighten_bounds_from_correctness Hcorrectness :=
  cbv beta iota zeta in Hcorrectness;
  lazymatch type of Hcorrectness with
  | forall v v', _ -> Bounds.is_bounded_by ?tighter_bounds _ /\ _
    => pretighten_bounds tighter_bounds
  end.
Ltac tighten_bounds_from_correctness Hcorrectness :=
  pretighten_bounds_from_correctness Hcorrectness; posttighten_bounds.
Ltac specialize_Hcorrectness Hcorrectness :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds (Interp _ ?fZ ?v')
         /\ cast_back_flat_const ?fW = Interp _ ?fZ ?v' ]
    => let v := lazymatch v' with cast_back_flat_const ?v => v end in
       specialize (Hcorrectness v' v);
       lazymatch type of Hcorrectness with
       | ?T -> Bounds.is_bounded_by _ _ /\ cast_back_flat_const ?fW' = _
         => let fWev := (eval cbv delta [fW] in fW) in
            unify fWev fW'; cut T
       end;
       [ let H := fresh in intro H; specialize (Hcorrectness H) | ]
  end.
Ltac handle_bounds_from_hyps :=
  repeat match goal with
         | _ => assumption
         | [ |- cast_back_flat_const _ = cast_back_flat_const _ ] => reflexivity
         | [ |- _ /\ _ ] => split
         | [ |- Bounds.is_bounded_by (_, _) _ ] => split
         end.
Ltac do_pre_wf_pipeline :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds (Interp _ ?fZ ?v')
         /\ cast_back_flat_const ?fW = Interp _ ?fZ ?v' ]
    => rewrite <- !(InterpPreWfPipeline fZ);
       let fZ' := fresh fZ in
       rename fZ into fZ';
       set (fZ := PreWfPipeline fZ');
       vm_compute in fZ; clear fZ'
  end.
Ltac do_reify := [ > reify_sig | cbv beta iota in * ].
Ltac do_post_wf_pipeline :=
  let Hcorrectness := fresh "Hcorrectness" in
  do_pose_correctness Hcorrectness;
  tighten_bounds_from_correctness Hcorrectness;
  specialize_Hcorrectness Hcorrectness;
  [ exact Hcorrectness
  | handle_bounds_from_hyps ].

Ltac do_reflective_pipeline :=
  assert_reflective;
  do_reify;
  do_pre_wf_pipeline;
  assert_wf;
  do_post_wf_pipeline.
