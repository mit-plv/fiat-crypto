(** * A reflective Version of [Wf] proofs *)
(** Because every constructor of [Syntax.wff] stores the syntax tree
    being proven well-formed, a proof that a syntax tree is
    well-formed is quadratic in the size of the syntax tree.  (Tacking
    an extra term on to the head of the syntax tree requires an extra
    constructor of [Syntax.wff], and that constructor stores the
    entirety of the new syntax tree.)

    In practice, this makes proving well-formedness of large trees
    very slow.  To remedy this, we provide an alternative type
    ([reflect_wffT]) that implies [Syntax.wff], but is only linear in
    the size of the syntax tree, with a coefficient less than 1.

    The idea is that, since we already know the syntax-tree arguments
    to the constructors (and, moreover, already fully know the shape
    of the [Syntax.wff] proof, because it will exactly match the shape
    of the syntax tree), the proof doesn't have to store any of that
    information.  It only has to store the genuinely new information
    in [Syntax.wff], namely, that the constants don't depend on the
    [var] argument (i.e., that the constants in the same location in
    the two expressions are equal), and that there are no free nor
    mismatched variables (i.e., that the variables in the same
    location in the two expressions are in the relevant list of
    binders).  We can make the further optimization of storing the
    location in the list of each binder, so that all that's left to
    verify is that the locations line up correctly.

    Since there is no way to assign list locations (De Bruijn indices)
    after the fact (that is, once we have an [exprf var t] rather than
    an [Expr t]), we instead start from an expression where [var] is
    enriched with De Bruijn indices, and talk about [Syntax.wff] of
    that expression stripped of its De Bruijn indices.  Since this
    procedure is only expected to work on concrete syntax trees, we
    will be able to simply check by unification to check that
    stripping the indices results in the term that we started with.

    The interface of this file is that, to prove a [Syntax.Wf] goal,
    you invoke the tactic [reflect_Wf base_type_eq_semidec_is_dec
    op_beq_bl], where:

    - [base_type_eq_semidec_is_dec : forall t1 t2,
       base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2] for
       some [base_type_eq_semidec_transparent : forall t1 t2 :
       base_type_code, option (t1 = t2)], and

    - [op_beq_bl : forall t1 tR x y, prop_of_option (op_beq t1 tR x y)
      -> x = y] for some [op_beq : forall t1 tR, op t1 tR -> op t1 tR
      -> reified_Prop] *)

Require Import Coq.Arith.Arith Coq.Logic.Eqdep_dec.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.EtaWf.
Require Import Crypto.Reflection.WfReflectiveGen.
Require Import Crypto.Util.Notations Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod Crypto.Util.Decidable Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Export Crypto.Util.PartiallyReifiedProp. (* export for the [bool >-> reified_Prop] coercion *)
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
  Context (base_type_eq_semidec_transparent : forall t1 t2 : base_type_code, option (t1 = t2)).
  Context (base_type_eq_semidec_is_dec : forall t1 t2, base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  (** In practice, semi-deciding equality of operators should either
      return [Some trivial] or [None], and not make use of the
      generality of [pointed_Prop].  However, we need to use
      [pointed_Prop] internally because we need to talk about equality
      of things of type [var t], for [var : base_type_code -> Type].
      It does not hurt to allow extra generality in [op_beq]. *)
  Context (op_beq : forall t1 tR, op t1 tR -> op t1 tR -> reified_Prop).
  Context (op_beq_bl : forall t1 tR x y, to_prop (op_beq t1 tR x y) -> x = y).
  Context {var1 var2 : base_type_code -> Type}.

  Local Notation eP := (fun t => var1 (fst t) * var2 (snd t))%type (only parsing).

  (* convenience notations that fill in some arguments used across the section *)
  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation duplicate_type := (@duplicate_type base_type_code var1 var2).
  Local Notation reflect_wffT := (@reflect_wffT base_type_code base_type_eq_semidec_transparent op op_beq var1 var2).
  Local Notation reflect_wfT := (@reflect_wfT base_type_code base_type_eq_semidec_transparent op op_beq var1 var2).
  Local Notation flat_type_eq_semidec_transparent := (@flat_type_eq_semidec_transparent base_type_code base_type_eq_semidec_transparent).
  Local Notation preflatten_binding_list2 := (@preflatten_binding_list2 base_type_code base_type_eq_semidec_transparent var1 var2).
  Local Notation type_eq_semidec_transparent := (@type_eq_semidec_transparent base_type_code base_type_eq_semidec_transparent).

  Local Ltac handle_op_beq_correct :=
    repeat match goal with
           | [ H : to_prop (op_beq ?t1 ?tR ?x ?y) |- _ ]
             => apply op_beq_bl in H
           end.
  Local Ltac t_step :=
    match goal with
    | [ |- True ] => exact I
    | _ => progress cbv beta delta [eq_type_and_var op_beq' flatten_binding_list2 WfReflectiveGen.preflatten_binding_list2 option_map eq_semidec_and_gen] in *
    | _ => progress simpl in *
    | _ => progress subst
    | _ => progress break_innermost_match_step
    | _ => progress inversion_option
    | _ => progress inversion_prod
    | _ => progress inversion_reified_Prop
    | _ => congruence
    | _ => tauto
    | _ => progress intros
    | _ => progress handle_op_beq_correct
    | _ => progress specialize_by tauto
    | [ v : ex _ |- _ ] => destruct v
    | [ v : sigT _ |- _ ] => destruct v
    | [ v : prod _ _ |- _ ] => destruct v
    | [ H : forall x x', _ |- wff (flatten_binding_list ?x1 ?x2 ++ _)%list _ _ ]
      => specialize (H x1 x2)
    | [ H : forall x x', _ |- wf (existT _ _ (?x1, ?x2) :: _)%list _ _ ]
      => specialize (H x1 x2)
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : to_prop (_ /\ _) |- _ ] => apply to_prop_and_reified_Prop in H; destruct H
    | [ H : context[duplicate_type (_ ++ _)%list] |- _ ]
      => rewrite duplicate_type_app in H
    | [ H : context[List.length (duplicate_type _)] |- _ ]
      => rewrite duplicate_type_length in H
    | [ H : context[List.length (_ ++ _)%list] |- _ ]
      => rewrite List.app_length in H
    | [ |- wff _ (unnatize_exprf (fst _) _) (unnatize_exprf (fst _) _) ]
      => erewrite length_natize_interp_flat_type1, length_natize_interp_flat_type2; eassumption
    | [ |- wf _ (unnatize_exprf (fst _) _) (unnatize_exprf (fst _) _) ]
      => erewrite length_natize_interp_flat_type1, length_natize_interp_flat_type2; eassumption
    | [ H : base_type_eq_semidec_transparent _ _ = None |- False ] => eapply duplicate_type_not_in; eassumption
    | [ H : List.nth_error _ _ = Some _ |- _ ] => apply List.nth_error_In in H
    | [ H : List.In _ (duplicate_type _) |- _ ] => eapply duplicate_type_in in H; [ | eassumption.. ]
    | [ H : context[match _ with _ => _ end] |- _ ] => revert H; progress break_innermost_match
    | [ |- wff _ _ _ ] => constructor
    | [ |- wf _ _ ] => constructor
    | _ => progress unfold and_reified_Prop in *
    | [ |- wff (flatten_binding_list ?x ?y) _ _ ]
      => rewrite <- (List.app_nil_r (flatten_binding_list x y))
    end.
  Local Ltac t := repeat t_step.
  Fixpoint reflect_wff (G : list (sigT (fun t => var1 t * var2 t)%type))
           {t1 t2 : flat_type}
           (e1 : @exprf (fun t => nat * var1 t)%type t1) (e2 : @exprf (fun t => nat * var2 t)%type t2)
           {struct e1}
    : let reflective_obligation := reflect_wffT (duplicate_type G) e1 e2 in
      match flat_type_eq_semidec_transparent t1 t2 with
      | Some p
        => to_prop reflective_obligation
          -> @wff base_type_code op var1 var2 G t2 (eq_rect _ exprf (unnatize_exprf (List.length G) e1) _ p) (unnatize_exprf (List.length G) e2)
      | None => True
      end.
  Proof.
    cbv zeta.
    destruct e1 as [ | | ? ? ? args | tx ex tC eC | ? ex ? ey ],
                   e2 as [ | | ? ? ? args' | tx' ex' tC' eC' | ? ex' ? ey' ]; simpl;
      try solve [ break_match; solve [ exact I | intros [] ] ];
      [ clear reflect_wff
      | clear reflect_wff
      | specialize (reflect_wff G _ _ args args')
      | pose proof (reflect_wff G _ _ ex ex');
        pose proof (fun x x'
                    => match preflatten_binding_list2 tx tx' as v return match v with Some _ => _ | None => True end with
                      | Some G0
                        => reflect_wff
                            (G0 x x' ++ G)%list _ _
                            (eC (snd (natize_interp_flat_type (length (duplicate_type G)) x)))
                            (eC' (snd (natize_interp_flat_type (length (duplicate_type G)) x')))
                      | None => I
                      end);
        clear reflect_wff
      | pose proof (reflect_wff G _ _ ex ex'); pose proof (reflect_wff G _ _ ey ey'); clear reflect_wff ].
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
  Qed.
  Definition reflect_wf
           {t1 t2 : type}
           (e1 : @expr (fun t => nat * var1 t)%type t1) (e2 : @expr (fun t => nat * var2 t)%type t2)
    : let reflective_obligation := reflect_wfT nil e1 e2 in
      match type_eq_semidec_transparent t1 t2 with
      | Some p
        => to_prop reflective_obligation
          -> @wf base_type_code op var1 var2 t2 (eq_rect _ expr (unnatize_expr 0 e1) _ p) (unnatize_expr 0 e2)
      | None => True
      end.
  Proof.
    destruct e1 as [ tx tR f ],
                   e2 as [ tx' tR' f' ]; simpl; try solve [ exact I ].
    pose proof (fun x x'
                => match preflatten_binding_list2 tx tx' as v return match v with Some _ => _ | None => True end with
                   | Some G0
                     => reflect_wff
                          (G0 x x' ++ nil)%list
                          (f (snd (natize_interp_flat_type 0 x)))
                          (f' (snd (natize_interp_flat_type 0 x')))
                   | None => I
                   end).
    t.
  Qed.
End language.

Section Wf.
  Context (base_type_code : Type)
          (base_type_eq_semidec_transparent : forall t1 t2 : base_type_code, option (t1 = t2))
          (base_type_eq_semidec_is_dec : forall t1 t2, base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (op_beq : forall t1 tR, op t1 tR -> op t1 tR -> reified_Prop)
          (op_beq_bl : forall t1 tR x y, to_prop (op_beq t1 tR x y) -> x = y)
          {t : type base_type_code}
          (e : @Expr base_type_code op t).

  (** Leads to smaller proofs, but is less generally applicable *)
  Theorem reflect_Wf_unnatize
    : (forall var1 var2,
          to_prop (@reflect_wfT base_type_code base_type_eq_semidec_transparent op op_beq var1 var2 nil t t (e _) (e _)))
      -> Wf (fun var => unnatize_expr 0 (e (fun t => (nat * var t)%type))).
  Proof.
    intros H var1 var2; specialize (H var1 var2).
    pose proof (@reflect_wf base_type_code base_type_eq_semidec_transparent base_type_eq_semidec_is_dec op op_beq op_beq_bl var1 var2 t t (e _) (e _)) as H'.
    rewrite type_eq_semidec_transparent_refl in H' by assumption; simpl in *.
    edestruct @reflect_wfT; simpl in *; tauto.
  Qed.

  (** Leads to larger proofs (an extra constant factor which is the
      size of the expression tree), but more generally applicable *)
  Theorem reflect_Wf
    : (forall var1 var2,
          unnatize_expr 0 (e (fun t => (nat * var1 t)%type)) = e _
          /\ to_prop (@reflect_wfT base_type_code base_type_eq_semidec_transparent op op_beq var1 var2 nil t t (e _) (e _)))
      -> Wf e.
  Proof.
    intros H var1 var2.
    rewrite <- (proj1 (H var1 var2)), <- (proj1 (H var2 var2)).
    apply reflect_Wf_unnatize, H.
  Qed.
End Wf.

(** Using [ExprEta'] ensures that reduction and conversion don't block
    on destructuring the variable arguments. *)
Ltac preapply_eta'_Wf :=
  lazymatch goal with
  | [ |- @Wf ?base_type_code ?op ?t ?e ]
    => apply (proj1 (@Wf_ExprEta'_iff base_type_code op t e))
  end.
Ltac generalize_reflect_Wf base_type_eq_semidec_is_dec op_beq_bl :=
  lazymatch goal with
  | [ |- @Wf ?base_type_code ?op ?t ?e ]
    => generalize (@reflect_Wf_unnatize base_type_code _ base_type_eq_semidec_is_dec op _ op_beq_bl t e)
  end.
Ltac use_reflect_Wf :=
  let H := fresh in
  intro H;
  lazymatch type of H with
  | ?A -> ?B
    => cut A
  end;
  [ abstract vm_cast_no_check H
  | clear H ].
Ltac fin_reflect_Wf :=
  intros;
  lazymatch goal with
  | [ |- to_prop ?P ]
    => replace P with (trueify P) by abstract vm_cast_no_check (eq_refl P)
  end;
  apply trueify_true.
(** The tactic [reflect_Wf] is the main tactic of this file, used to
    prove [Syntax.Wf] goals *)
Ltac reflect_Wf base_type_eq_semidec_is_dec op_beq_bl :=
  preapply_eta'_Wf;
  generalize_reflect_Wf base_type_eq_semidec_is_dec op_beq_bl;
  use_reflect_Wf; fin_reflect_Wf.
