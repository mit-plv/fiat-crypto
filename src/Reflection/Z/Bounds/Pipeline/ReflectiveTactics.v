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
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.RenameBinders.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.Z.Bounds.Relax.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.Composition.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstLet.
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
  Export Crypto.Reflection.Reify. (* export for the instances for recursing under binders *)
  Export Crypto.Reflection.Z.Reify. (* export for the tactic redefinitions *)
  Export Crypto.Reflection.Z.Bounds.Pipeline.Definition.Exports.
End Exports.

(** ** Reification *)
(** The [do_reify] tactic handles goals of the form
<<
forall x, Interp _ ?e x = F
>>
    by reifying [F]. *)
Ltac do_reify :=
  cbv beta iota delta [Syntax.interp_flat_type Syntax.interp_base_type];
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
              Interp InterpEta interp_op interp interp_eta interpf interpf_step
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

(** The tactic [abstract_vm_compute_rhs] unifies [LHS] with the result
    of [vm_compute]ing [RHS], and costs two [vm_compute]s. *)
Ltac abstract_vm_compute_rhs :=
  intros; clear;
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let RHS' := (eval vm_compute in RHS) in
       unify LHS RHS'; clear;
       abstract vm_cast_no_check (eq_refl RHS')
  end.
(** The tactic [abstract_vm_compute_rhs_no_evar] costs only one
    [vm_compute] and proves only evar-free goals.  Best when the cost
    of retypechecking [RHS] is small, or at least smaller than the
    cost of retypechecking [LHS]. *)
Ltac abstract_vm_compute_rhs_no_evar :=
  intros; clear;
  match goal with
  | [ |- ?LHS = ?RHS ]
    => abstract vm_cast_no_check (eq_refl RHS)
  end.
(** The tactic [abstract_rhs] unifies [LHS] with [RHS]. *)
Ltac abstract_rhs :=
  intros; clear;
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => unify LHS RHS; clear;
       abstract exact_no_check (eq_refl RHS)
  end.
(** The tactic [renamify_rhs] calls [renamify] on [RHS] and unifies
    that with [LHS]; and then costs one [vm_compute] to prove the
    equality. *)
Ltac renamify_rhs :=
  intros; clear;
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let RHS' := renamify RHS in
       unify LHS RHS';
       clear; abstract vm_cast_no_check (eq_refl RHS')
  end.
(** The tactic [abstract_cbv_rhs] unfies [LHS] with the result of
    running [cbv] in [RHS], and costs a [cbv] and a [vm_compute].  Use
    this if you don't want to lose binder names or otherwise can't use
    [vm_compute]. *)
Ltac abstract_cbv_rhs :=
  intros; clear;
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let RHS' := (eval cbv in RHS) in
       unify LHS RHS';
       clear; abstract vm_cast_no_check (eq_refl RHS')
  end.
(** The tactic [abstract_cbv_interp_rhs] runs the interpretation
    reduction strategies in [RHS] and unifies the result with [LHS],
    and does not use the vm (and hence does not fully reduce things,
    which is important for efficiency). *)
Ltac abstract_cbv_interp_rhs :=
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

(** ** Assembling the Pipeline *)
(** The tactic [refine_with_pipeline_correct] uses the
    [PipelineCorrect] lemma to create side-conditions.  It assumes the
    goal is in exactly the form given in the conclusion of the
    [PipelineCorrect] lemma. *)
Ltac refine_with_pipeline_correct :=
  lazymatch goal with
  | [ |- _ /\ ?castback ?fW = ?fZ ?arg ]
    => let lem := open_constr:(@PipelineCorrect _ _ _ _ _ _ _ _ _ _ _ _) in
       simple refine (lem _ _ _ _ _ _ _ _ _ _ _ _);
       subst fW fZ
  end;
  [ eexists
  | cbv [proj1_sig].. ].
(** The tactic [solve_side_conditions] uses the above
    reduction-and-proving-equality tactics to prove the
    side-conditions of [PipelineCorrect].  Which tactic to use was
    chosen in the following way:

    - The default is [abstract_vm_compute_rhs]

    - If the goal has no evar, instead use
      [abstract_vm_compute_rhs_no_evar] (it's faster)

    - If the [RHS] is already in [vm_compute]d form, use
      [abstract_rhs] (saves a needless [vm_compute] which would be a
      costly no-op)

    - If the proof needs to be transparent and there are no evars and
      you want the user to see the fully [vm_compute]d term on error,
      use [vm_compute; reflexivity]

    - If the user should see an unreduced term and you're proving [_ =
      true], use [abstract vm_cast_no_check (eq_refl true)]

    - If you want to preserve binder names, use [abstract_cbv_rhs]

    The other choices are tactics that are specialized to the specific
    side-condition for which they are used (reification, boundedness
    of input, reduction of [Interp], renaming). *)
Ltac solve_side_conditions :=
  [>
   (** ** reification *)
   do_reify |
   (** ** pre-wf pipeline *)
   abstract_vm_compute_rhs |
   (** ** reflective wf side-condition 1 *)
   abstract_vm_compute_rhs_no_evar |
   (** ** reflective wf side-condition 2 *)
   abstract_vm_compute_rhs_no_evar |
   (** ** post-wf pipeline *)
   abstract_vm_compute_rhs |
   (** ** post-wf pipeline gives [Some _] *)
   abstract_rhs |
   (** ** renaming binders *)
   renamify_rhs |
   (** ** types computed from given output bounds are the same as types computed from computed output bounds *)
   (** N.B. the proof must be exactly [eq_refl] because it's used in a
            later goal and needs to reduce *)
   subst_let; clear; vm_compute; reflexivity |
   (** ** computed output bounds are not looser than the given output bounds *)
   (** we do subst and we don't [vm_compute] first because we want to
       get an error message that displays the bounds *)
   subst_let; clear; abstract vm_cast_no_check (eq_refl true) |
   (** ** removal of a cast across the equality proof above *)
   abstract_cbv_rhs |
   (** ** unfolding of [interp] constants *)
   abstract_cbv_interp_rhs |
   (** ** boundedness of inputs *)
   abstract handle_bounds_from_hyps ].


(** ** The Entire Pipeline *)
(** The [do_reflective_pipeline] tactic solves a goal of the form that
    is described at the top of this file, and is the public interface
    of this file. *)
Ltac do_reflective_pipeline :=
  refine_with_pipeline_correct; solve_side_conditions.
