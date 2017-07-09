(** * Reflective Pipeline: Tactics that execute the pipeline *)
(** N.B. This file should not need to be changed in normal
    modifications of the reflective transformations; to modify the
    transformations performed in the reflective pipeline; see
    Pipeline/Definition.v.  If the input format of the pre-reflective
    goal changes, prefer adding complexity to Pipeline/Glue.v to
    transform the goal and hypotheses into a uniform syntax to
    modifying this file.  This file will need to be modified if you
    perform heavy changes in the shape of the generic or ℤ-specific
    reflective machinery itself, or if you find bugs or slowness. *)
(** ** Preamble *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfReflective.
Require Import Crypto.Compilers.RenameBinders.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.Relax.
Require Import Crypto.Compilers.Reify.
Require Import Crypto.Compilers.Z.Reify.
Require Import Crypto.Compilers.InterpSideConditions.
Require Import Crypto.Compilers.Z.InterpSideConditions.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstLet.
Require Import Crypto.Util.Tactics.UnfoldArg.
Require Import Crypto.Util.Tactics.UnifyAbstractReflexivity.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Option.
Require Import Bedrock.Word.

(** The final tactic in this file, [do_reflective_pipeline], takes a
    goal of the form
<<
@Bounds.is_bounded_by (codomain T) bounds (fZ (cast_back_flat_const v))
  /\ cast_back_flat_const fW = fZ (cast_back_flat_const v)
>>

    where [fW] must be a context definition which is a single evar,
    and all other terms must be evar-free.  It fully solves the goal,
    instantiating [fW] with an appropriately-unfolded
    (reflection-definition-free) version of [fZ (cast_back_flat_const
    v)] which has been transformed by the reflective pipeline. *)

Module Export Exports.
  Export Crypto.Compilers.Reify. (* export for the instances for recursing under binders *)
  Export Crypto.Compilers.Z.Reify. (* export for the tactic redefinitions *)
  Export Crypto.Compilers.Z.Bounds.Pipeline.Definition.Exports.
End Exports.

(** ** Reification *)
(** The [do_reify] tactic handles goals of the form
<<
forall x, Interp _ ?e x = F
>>
    by reifying [F]. *)
Ltac do_reify :=
  unfold_second_arg Tuple.tuple;
  unfold_second_arg Tuple.tuple';
  cbv beta iota delta [Tuple.tuple Tuple.tuple'] in *;
  cbv beta iota delta [Syntax.interp_flat_type Syntax.interp_base_type];
  reify_context_variables;
  Reify_rhs; reflexivity.
(** ** Input Boundedness Side-Conditions *)
(** The tactic [handle_bounds_from_hyps] handles goals of the form
<<
Bounds.is_bounded_by (_, _, ..., _) _
>>
     by splitting them apart and looking in the context for hypotheses
     that prove the bounds. *)
Ltac handle_bounds_from_hyps :=
  repeat match goal with
         | _ => assumption
         | [ |- cast_back_flat_const _ = cast_back_flat_const _ ] => reflexivity
         | [ |- _ /\ _ ] => split
         | [ |- Bounds.is_bounded_by (_, _) _ ] => split
         end.
(** ** Unfolding [Interp] *)
(** The reduction strategies [interp_red], [extra_interp_red], and
    [constant_simplification] (the latter two defined in
    Pipeline/Definition.v) define the constants that get unfolded
    before instantiating the original evar with [Interp _
    vm_computed_reified_expression arguments]. *)
Declare Reduction interp_red
  := cbv [fst snd
              Interp (*InterpEta interp_op*) interp interp_eta interpf interpf_step
              interp_flat_type_eta interp_flat_type_eta_gen interp_flat_type
              interp_base_type interp_op
              SmartMap.SmartFlatTypeMap SmartMap.SmartFlatTypeMapUnInterp SmartMap.SmartFlatTypeMapInterp2
              SmartMap.smart_interp_flat_map
              codomain domain
              lift_op Zinterp_op cast_const
              ZToInterp interpToZ
         ].

(** ** Solving Side-Conditions of Equality *)
(** This section defines a number of different ways to solve goals of
    the form [LHS = RHS] where [LHS] may contain evars and [RHS] must
    not contain evars.  Most tactics use [abstract] to reduce the load
    on [Defined] and to catch looping behavior early. *)

(** The tactic [unify_abstract_renamify_rhs_reflexivity] calls [renamify] on [RHS] and unifies
    that with [LHS]; and then costs one [vm_compute] to prove the
    equality. *)
Ltac unify_abstract_renamify_rhs_reflexivity :=
  unify_transformed_rhs_abstract_tac
    ltac:(renamify)
           unify_tac
           vm_cast_no_check.
(** The tactic [unify_abstract_cbv_interp_rhs_reflexivity] runs the interpretation
    reduction strategies in [RHS] and unifies the result with [LHS],
    and does not use the vm (and hence does not fully reduce things,
    which is important for efficiency). *)
Ltac unify_abstract_cbv_interp_rhs_reflexivity :=
  intros; clear;
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let RHS' := (eval interp_red in RHS) in
       let RHS' := (eval extra_interp_red in RHS') in
       let RHS' := lazymatch do_constant_simplification with
                   | true => (eval constant_simplification in RHS')
                   | _ => RHS'
                   end in
       unify LHS RHS'; abstract exact_no_check (eq_refl RHS')
  end.

(** *** Boundedness Lemma Side Conditions *)
(** The tactic [handle_boundedness_side_condition] unfolds relevant
    identifiers in the side-condition of the boundedness lemma.  It
    then calls [boundedness_side_condition_solver], which can be
    overridden. *)
(** The tactic [boundedness_side_condition_solver] attempts to solve
    the algebraic side conditions of the boundedness lemma; it leaves
    them over if it cannot solve them. *)
Ltac boundedness_side_condition_solver :=
  repeat match goal with
         | [ |- _ /\ _ ] => apply conj
         | [ |- ?x = ?x ] => reflexivity
         end;
  try abstract ring.
Ltac handle_boundedness_side_condition :=
  (** TODO: This next bit, with repeat intros [? ?], could be done
        with a single [apply], if we make the right lemma.  We should
        write that lemma. *)
  cbv [PointedProp.to_prop Syntax.interp_flat_type Syntax.interp_base_type Syntax.domain Syntax.codomain];
  repeat match goal with
         | [ |- forall x : _ * _, _ ]
           => let a := fresh in let b := fresh in intros [a b]; revert a b
         | [ |- forall x, _ ]
           => let x := fresh "x" in intro x
         end;
  cbv [id
         fst snd
         InterpSideConditions Compilers.InterpSideConditions.InterpSideConditions interp_side_conditions interpf_side_conditions interpf_side_conditions_gen
         Z.Syntax.Util.interped_op_side_conditions
         ExprInversion.invert_Abs
         Syntax.interp_op Syntax.lift_op
         Syntax.Zinterp_op
         SmartMap.SmartFlatTypeMapUnInterp SmartMap.SmartValf SmartMap.SmartFlatTypeMapInterp2
         Syntax.cast_const Syntax.ZToInterp Syntax.interpToZ];
  cbv [PointedProp.and_pointed_Prop];
  try match goal with
      | [ |- True ] => exact I
      end;
  boundedness_side_condition_solver.

(** ** Assemble the parts of Pipeline.Definition, in Gallina *)
(** In this section, we assemble [PreWfPipeline] and [PostWfPipeline],
    and add extra equality hypotheses to minimize the work we have to
    do in Ltac. *)
(** *** Gallina assembly imports *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfReflectiveGen.
Require Import Crypto.Compilers.WfReflective.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaWf.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.OutputType.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.Relax.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.PartiallyReifiedProp.
Require Import Crypto.Util.Equality.

(** *** Gallina assembly *)
Section with_round_up_list.
  Context {allowable_lgsz : list nat}.

  Local Notation pick_typeb := (@Bounds.bounds_to_base_type (Bounds.round_up_to_in_list allowable_lgsz)) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).

  Definition PipelineCorrect
             opts
             {t}
             {input_bounds : interp_flat_type Bounds.interp_base_type (domain t)}
             {given_output_bounds : interp_flat_type Bounds.interp_base_type (codomain t)}
             {v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds)}
             {b e' e_final e_final_newtype}
             {fZ}
             {final_e_evar : interp_flat_type Syntax.interp_base_type (pick_type given_output_bounds)}
             {e}
             {e_pre_pkg}
             {e_pkg}
             (** ** reification *)
             (rexpr_sig : { rexpr : Expr base_type op t | forall x, Interp Syntax.interp_op rexpr x = fZ x })
             (** ** pre-wf pipeline *)
             (He : e = PreWfPipeline (proj1_sig rexpr_sig))
             (** ** proving wf *)
             (He_unnatize_for_wf : forall var, unnatize_expr 0 (ExprEta' e (fun t => (nat * var t)%type)) = ExprEta' e _)
             (Hwf : forall var1 var2,
                 let P := (@reflect_wfT base_type base_type_eq_semidec_transparent op op_beq var1 var2 nil _ _ (ExprEta' e _) (ExprEta' e _)) in
                 trueify P = P)
             (** ** post-wf-pre-bounds-pipeline *)
             (Hpost_wf_pre_bounds : e_pre_pkg = PostWfPreBoundsPipeline opts e)
             (** ** post-wf-pipeline *)
             (Hpost : e_pkg = PostWfBoundsPipeline _ opts e e_pre_pkg input_bounds)
             (Hpost_correct : Some {| input_expr := e ; input_bounds := input_bounds ; output_bounds := b ; output_expr := e' |} = e_pkg)
             (** ** renaming *)
             (Hrenaming : e_final = e')
             (** ** bounds relaxation *)
             (Hbounds_relax : Bounds.is_tighter_thanb b given_output_bounds = true)
             (Hbounds_sane : pick_type given_output_bounds = pick_type b)
             (Hbounds_sane_refl
              : e_final_newtype
                = eq_rect _ (fun t => Expr base_type op (Arrow (pick_type input_bounds) t)) e' _ (eq_sym Hbounds_sane))
             (** ** instantiation of original evar *)
             (Hevar : final_e_evar = InterpEta (t:=Arrow _ _) Syntax.interp_op e_final_newtype v')
             (** ** side conditions (boundedness) *)
             (Hv1 : Bounds.is_bounded_by input_bounds (cast_back_flat_const v'))
             (Hv2 : forall v, PointedProp.to_prop (InterpSideConditions e_pre_pkg v))
    : Bounds.is_bounded_by given_output_bounds (fZ (cast_back_flat_const v'))
      /\ cast_back_flat_const final_e_evar = fZ (cast_back_flat_const v').
  Proof.
    destruct rexpr_sig as [? Hrexpr].
    assert (Hwf' : Wf e)
      by (apply (proj1 (@Wf_ExprEta'_iff _ _ _ e));
          eapply reflect_Wf;
          [ .. | intros; split; [ eapply He_unnatize_for_wf | rewrite <- Hwf; apply trueify_true ] ];
          auto using base_type_eq_semidec_is_dec, op_beq_bl).
    clear Hwf He_unnatize_for_wf.
    symmetry in Hpost_correct.
    subst; cbv [proj1_sig] in *.
    rewrite eq_InterpEta, <- Hrexpr.
    eapply PostWfPipelineCorrect in Hpost_correct; [ | solve [ eauto ].. ].
    rewrite !@InterpPreWfPipeline in Hpost_correct.
    unshelve eapply relax_output_bounds; try eassumption; [].
    match goal with
    | [ |- context[Interp _ (@eq_rect ?A ?x ?P ?k ?y ?pf) ?v] ]
      => rewrite (@ap_transport A P _ x y pf (fun t e => Interp interp_op e v) k)
    end.
    rewrite <- transport_pp, concat_Vp; simpl.
    apply Hpost_correct.
  Qed.
End with_round_up_list.

(** ** Assembling the Pipeline, in Ltac *)
(** The tactic [refine_with_pipeline_correct] uses the
    [PipelineCorrect] lemma to create side-conditions.  It assumes the
    goal is in exactly the form given in the conclusion of the
    [PipelineCorrect] lemma. *)

Ltac refine_with_pipeline_correct opts :=
  lazymatch goal with
  | [ |- _ /\ ?castback ?fW = ?fZ ?arg ]
    => let lem := open_constr:(@PipelineCorrect _ opts _ _ _ _ _ _ _ _ _ _ _ _ _) in
       simple refine (lem _ _ _ _ _ _ _ _ _ _ _ _ _ _);
       subst fW fZ
  end;
  [ eexists
  | cbv [proj1_sig].. ].

(** The tactic [solve_side_conditions] uses the above
    reduction-and-proving-equality tactics to prove the
    side-conditions of [PipelineCorrect].  The order must match with
    [PipelineCorrect].  Which tactic to use was chosen in the
    following way:

    - The default is [unify_abstract_vm_compute_rhs_reflexivity]

    - If the [RHS] is already in [vm_compute]d form, use
      [unify_abstract_rhs_reflexivity] (saves a needless [vm_compute] which would be a
      costly no-op)

    - If the proof needs to be transparent and there are no evars and
      you want the user to see the fully [vm_compute]d term on error,
      use [vm_compute; reflexivity]

    - If the user should see an unreduced term and you're proving [_ =
      true], use [abstract vm_cast_no_check (eq_refl true)]

    - If you want to preserve binder names, use [unify_abstract_cbv_rhs_reflexivity]

    The other choices are tactics that are specialized to the specific
    side-condition for which they are used (reification, boundedness
    of input, reduction of [Interp], renaming). *)
Ltac solve_side_conditions :=
  [>
   (** ** reification *)
   do_reify |
   (** ** pre-wf pipeline *)
   unify_abstract_vm_compute_rhs_reflexivity |
   (** ** reflective wf side-condition 1 *)
   unify_abstract_vm_compute_rhs_reflexivity |
   (** ** reflective wf side-condition 2 *)
   unify_abstract_vm_compute_rhs_reflexivity |
   (** ** post-wf-pre-bounds-pipeline *)
   unify_abstract_vm_compute_rhs_reflexivity |
   (** ** post-wf pipeline *)
   unify_abstract_vm_compute_rhs_reflexivity |
   (** ** post-wf pipeline gives [Some _] *)
   unify_abstract_rhs_reflexivity |
   (** ** renaming binders *)
   unify_abstract_renamify_rhs_reflexivity |
   (** ** computed output bounds are not looser than the given output bounds *)
   (** we do subst and we don't [vm_compute] first because we want to
       get an error message that displays the bounds *)
   subst_let; clear; abstract vm_cast_no_check (eq_refl true) |
   (** ** types computed from given output bounds are the same as types computed from computed output bounds *)
   (** N.B. the proof must be exactly [eq_refl] because it's used in a
            later goal and needs to reduce *)
   subst_let; clear; vm_compute; reflexivity |
   (** ** removal of a cast across the equality proof above *)
   unify_abstract_compute_rhs_reflexivity |
   (** ** unfolding of [interp] constants *)
   unify_abstract_cbv_interp_rhs_reflexivity |
   (** ** boundedness of inputs *)
   abstract handle_bounds_from_hyps |
   (** ** boundedness side-condition *)
   handle_boundedness_side_condition ].


(** ** The Entire Pipeline *)
(** The [do_reflective_pipeline] tactic solves a goal of the form that
    is described at the top of this file, and is the public interface
    of this file. *)
Ltac do_reflective_pipeline opts :=
  refine_with_pipeline_correct opts; solve_side_conditions.
Notation default_PipelineOptions := default_PipelineOptions.
