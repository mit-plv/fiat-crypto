(** * Reflective Pipeline: Assemble the parts of Pipeline.Definition, in Gallina *)
(** In this file, we assemble [PreWfPipeline] and [PostWfPipeline],
    and add extra equality hypotheses to minimize the work we have to
    do in Ltac. *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfReflectiveGen.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.OutputType.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.Z.Bounds.Relax.
Require Import Crypto.Util.PartiallyReifiedProp.
Require Import Crypto.Util.Equality.

Module Export Exports.
  Export Pipeline.Definition.Exports.
End Exports.

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).
Definition PipelineCorrect
           {t}
           {input_bounds : interp_flat_type Bounds.interp_base_type (domain t)}
           {given_output_bounds : interp_flat_type Bounds.interp_base_type (codomain t)}
           {v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds)}
           {b e' e_final e_final_newtype}
           {fZ}
           {final_e_evar : interp_flat_type Syntax.interp_base_type (pick_type given_output_bounds)}
           {e}
           {e_pkg}
           (** ** reification *)
           (rexpr_sig : { rexpr : Expr base_type op t | forall x, Interp Syntax.interp_op rexpr x = fZ x })
           (** ** pre-wf pipeline *)
           (He : e = PreWfPipeline (proj1_sig rexpr_sig))
           (** ** proving wf *)
           (He_unnatize_for_wf : forall var, unnatize_expr 0 (e (fun t => (nat * var t)%type)) = e _)
           (Hwf : forall var1 var2,
               let P := (@reflect_wfT base_type base_type_eq_semidec_transparent op op_beq var1 var2 nil _ _ (e _) (e _)) in
               trueify P = P)
           (** ** post-wf-pipeline *)
           (Hpost : e_pkg = PostWfPipeline e input_bounds)
           (Hpost_correct : e_pkg = Some {| input_expr := e ; input_bounds := input_bounds ; output_bounds := b ; output_expr := e' |})
           (** ** renaming *)
           (Hrenaming : e_final = e')
           (** ** bounds relaxation *)
           (Hbounds_sane : pick_type given_output_bounds = pick_type b)
           (Hbounds_relax : Bounds.is_tighter_thanb b given_output_bounds = true)
           (Hbounds_sane_refl
            : e_final_newtype
              = eq_rect _ (fun t => Expr base_type op (Arrow (pick_type input_bounds) t)) e' _ (eq_sym Hbounds_sane))
           (** ** instantiation of original evar *)
           (Hevar : final_e_evar = Interp (t:=Arrow _ _) Syntax.interp_op e_final_newtype v')
           (** ** side condition *)
           (Hv : Bounds.is_bounded_by input_bounds (cast_back_flat_const v'))
  : Bounds.is_bounded_by given_output_bounds (fZ (cast_back_flat_const v'))
    /\ cast_back_flat_const final_e_evar = fZ (cast_back_flat_const v').
Proof.
  destruct rexpr_sig as [? Hrexpr].
  assert (Hwf' : Wf e)
    by (eapply reflect_Wf;
        [ .. | intros; split; [ eapply He_unnatize_for_wf | rewrite <- Hwf; apply trueify_true ] ];
        auto using base_type_eq_semidec_is_dec, op_beq_bl).
  clear Hwf He_unnatize_for_wf.
  subst; cbv [proj1_sig] in *.
  rewrite <- Hrexpr.
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
