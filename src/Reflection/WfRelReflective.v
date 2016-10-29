(** * A reflective Version of [WfRel] proofs *)
(** See [WfReflective.v] and [WfReflectiveGen.v] for comments. *)
Require Import Coq.Arith.Arith Coq.Logic.Eqdep_dec.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.WfRel.
Require Import Crypto.Reflection.WfReflectiveGen.
Require Import Crypto.Util.Notations Crypto.Util.Tactics Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod Crypto.Util.Decidable Crypto.Util.ListUtil.
Require Export Crypto.Util.PointedProp. (* export for the [bool >-> option pointed_Prop] coercion *)
Require Export Crypto.Util.FixCoqMistakes.


Section language.
  (** To be able to optimize away so much of the [Syntax.wff] proof,
      we must be able to decide a few things: equality of base types,
      and equality of operator codes.  Since we will be casting across
      the equality proofs of base types, we require that this
      semi-decider give transparent proofs.  (This requirement is not
      enforced, but it will block [vm_compute] when trying to use the
      lemma in this file.) *)
  Context (base_type_code : Type).
  Context (interp_base_type1 interp_base_type2 : base_type_code -> Type).
  Context (base_type_eq_semidec_transparent : forall t1 t2 : base_type_code, option (t1 = t2)).
  Context (base_type_eq_semidec_is_dec : forall t1 t2, base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (R : forall t, interp_base_type1 t -> interp_base_type2 t -> Prop).
  (** In practice, semi-deciding equality of operators should either
      return [Some trivial] or [None], and not make use of the
      generality of [pointed_Prop].  However, we need to use
      [pointed_Prop] internally because we need to talk about equality
      of things of type [var t], for [var : base_type_code -> Type].
      It does not hurt to allow extra generality in [op_beq]. *)
  Context (op_beq : forall t1 tR, op t1 tR -> op t1 tR -> option pointed_Prop).
  Context (op_beq_bl : forall t1 tR x y, prop_of_option (op_beq t1 tR x y) -> x = y).
  Context {var1 var2 : base_type_code -> Type}.

  Local Notation eP := (fun t => var1 (fst t) * var2 (snd t))%type (only parsing).

  (* convenience notations that fill in some arguments used across the section *)
  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type1 := (interp_type interp_base_type1).
  Local Notation interp_type2 := (interp_type interp_base_type2).
  Local Notation interp_flat_type1 := (interp_flat_type interp_base_type1).
  Local Notation interp_flat_type2 := (interp_flat_type interp_base_type2).
  Local Notation exprf1 := (@exprf base_type_code interp_base_type1 op).
  Local Notation exprf2 := (@exprf base_type_code interp_base_type2 op).
  Local Notation expr1 := (@expr base_type_code interp_base_type1 op).
  Local Notation expr2 := (@expr base_type_code interp_base_type2 op).
  Local Notation duplicate_type := (@duplicate_type base_type_code var1 var2).
  Local Notation reflect_wffT := (@reflect_wffT base_type_code interp_base_type1 interp_base_type2 base_type_eq_semidec_transparent op R op_beq var1 var2).
  Local Notation reflect_wfT := (@reflect_wfT base_type_code interp_base_type1 interp_base_type2 base_type_eq_semidec_transparent op R op_beq var1 var2).
  Local Notation flat_type_eq_semidec_transparent := (@flat_type_eq_semidec_transparent base_type_code base_type_eq_semidec_transparent).
  Local Notation preflatten_binding_list2 := (@preflatten_binding_list2 base_type_code base_type_eq_semidec_transparent var1 var2).
  Local Notation type_eq_semidec_transparent := (@type_eq_semidec_transparent base_type_code base_type_eq_semidec_transparent).

  Local Ltac handle_op_beq_correct :=
    repeat match goal with
           | [ H : op_beq ?t1 ?tR ?x ?y = _ |- _ ]
             => let H' := fresh in
               pose proof (op_beq_bl t1 tR x y) as H'; rewrite H in H'; clear H
           end.
  Local Ltac t_step :=
    match goal with
    | _ => progress unfold eq_type_and_var, op_beq', flatten_binding_list2, preflatten_binding_list2, option_map, and_option_pointed_Prop, eq_semidec_and_gen in *
    | _ => progress simpl in *
    | _ => progress break_match
    | _ => progress subst
    | _ => progress inversion_option
    | _ => progress inversion_pointed_Prop
    | _ => congruence
    | _ => tauto
    | _ => progress intros
    | _ => progress handle_op_beq_correct
    | _ => progress specialize_by tauto
    | [ v : sigT _ |- _ ] => destruct v
    | [ v : prod _ _ |- _ ] => destruct v
    | [ H : forall x x', _ |- rel_wff _ (flatten_binding_list _ ?x1 ?x2 ++ _)%list _ _ ]
      => specialize (H x1 x2)
    | [ H : forall x x', _ |- rel_wf _ (existT _ _ (?x1, ?x2) :: _)%list _ _ ]
      => specialize (H x1 x2)
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : context[duplicate_type (_ ++ _)%list] |- _ ]
      => rewrite duplicate_type_app in H
    | [ H : context[List.length (duplicate_type _)] |- _ ]
      => rewrite duplicate_type_length in H
    | [ H : context[List.length (_ ++ _)%list] |- _ ]
      => rewrite List.app_length in H
    | [ |- rel_wff _ _ (unnatize_exprf (fst _) _) (unnatize_exprf (fst _) _) ]
      => erewrite length_natize_interp_flat_type1, length_natize_interp_flat_type2; eassumption
    | [ |- rel_wf _ _ (unnatize_exprf (fst _) _) (unnatize_exprf (fst _) _) ]
      => erewrite length_natize_interp_flat_type1, length_natize_interp_flat_type2; eassumption
    | [ H : base_type_eq_semidec_transparent _ _ = None |- False ] => eapply duplicate_type_not_in; eassumption
    | [ H : List.nth_error _ _ = Some _ |- _ ] => apply List.nth_error_In in H
    | [ H : List.In _ (duplicate_type _) |- _ ] => eapply duplicate_type_in in H; [ | eassumption.. ]
    | [ H : context[match _ with _ => _ end] |- _ ] => revert H; progress break_match
    | [ |- rel_wff _ _ _ _ ] => constructor
    | [ |- rel_wf _ _ _ _ ] => constructor
    | _ => progress unfold and_pointed_Prop in *
    end.
  Local Ltac t := repeat t_step.
  Fixpoint reflect_rel_wff (G : list (sigT (fun t => var1 t * var2 t)%type))
           {t1 t2 : flat_type}
           (e1 : @exprf1 (fun t => nat * var1 t)%type t1)
           (e2 : @exprf2 (fun t => nat * var2 t)%type t2)
           {struct e1}
    : match reflect_wffT (duplicate_type G) e1 e2, flat_type_eq_semidec_transparent t1 t2 with
      | Some reflective_obligation, Some p
        => to_prop reflective_obligation
          -> @rel_wff base_type_code interp_base_type1 interp_base_type2 op R var1 var2 G t2 (eq_rect _ exprf1 (unnatize_exprf (List.length G) e1) _ p) (unnatize_exprf (List.length G) e2)
      | _, _ => True
      end.
  Proof.
    destruct e1 as [ | | ? ? ? args | tx ex tC eC | ? ex ? ey ],
                   e2 as [ | | ? ? ? args' | tx' ex' tC' eC' | ? ex' ? ey' ]; simpl; try solve [ exact I ];
      [ clear reflect_rel_wff
      | clear reflect_rel_wff
      | specialize (reflect_rel_wff G _ _ args args')
      | pose proof (reflect_rel_wff G _ _ ex ex');
        pose proof (fun x x'
                    => match preflatten_binding_list2 tx tx' as v return match v with Some _ => _ | None => True end with
                      | Some G0
                        => reflect_rel_wff
                            (G0 x x' ++ G)%list _ _
                            (eC (snd (natize_interp_flat_type (length (duplicate_type G)) x)))
                            (eC' (snd (natize_interp_flat_type (length (duplicate_type G)) x')))
                      | None => I
                      end);
        clear reflect_rel_wff
      | pose proof (reflect_rel_wff G _ _ ex ex'); pose proof (reflect_rel_wff G _ _ ey ey'); clear reflect_rel_wff ].
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
  Qed.
  Fixpoint reflect_rel_wf (G : list (sigT (fun t => var1 t * var2 t)%type))
           {t1 t2 : type}
           (e1 : @expr1 (fun t => nat * var1 t)%type t1)
           (e2 : @expr2 (fun t => nat * var2 t)%type t2)
    : match reflect_wfT (duplicate_type G) e1 e2, type_eq_semidec_transparent t1 t2 with
      | Some reflective_obligation, Some p
        => to_prop reflective_obligation
          -> @rel_wf base_type_code interp_base_type1 interp_base_type2 op R var1 var2 G t2 (eq_rect _ expr1 (unnatize_expr (List.length G) e1) _ p) (unnatize_expr (List.length G) e2)
      | _, _ => True
      end.
  Proof.
    destruct e1 as [ t1 e1 | tx tR f ],
                   e2 as [ t2 e2 | tx' tR' f' ]; simpl; try solve [ exact I ];
      [ clear reflect_rel_wf;
        pose proof (@reflect_rel_wff G t1 t2 e1 e2)
      | pose proof (fun x x'
                    => match preflatten_binding_list2 tx tx' as v return match v with Some _ => _ | None => True end with
                      | Some G0
                        => reflect_rel_wf
                            (G0 x x' ++ G)%list _ _
                            (f (snd (natize_interp_flat_type (length (duplicate_type G)) x)))
                            (f' (snd (natize_interp_flat_type (length (duplicate_type G)) x')))
                      | None => I
                      end);
        clear reflect_rel_wf ].
    { t. }
    { t. }
  Qed.
End language.
