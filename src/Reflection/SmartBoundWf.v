Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.SmartBound.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.SmartCast.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_base_type_bounds : base_type_code -> Type)
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (bound_base_type : forall t, interp_base_type_bounds t -> base_type_code)
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (genericize_op : forall src dst (opc : op src dst) (new_bounded_type_in new_bounded_type_out : base_type_code),
              option { src'dst' : _ & op (fst src'dst') (snd src'dst') })
          (failf : forall var t, @exprf base_type_code op var (Tbase t))
          (wff_Cast : forall var1 var2 G A A' e1 e2,
              wff G e1 e2 -> wff G (Cast var1 A A' e1) (Cast var2 A A' e2)).

  Local Notation Expr := (@Expr base_type_code op).
  Local Notation SmartBound := (@SmartBound _ _ _ interp_op_bounds bound_base_type Cast).
  Local Notation smart_bound := (@smart_bound _ _ interp_base_type_bounds bound_base_type Cast).
  Local Notation UnSmartArrow := (@UnSmartArrow _ interp_base_type_bounds bound_base_type).
  Local Notation interpf_smart_bound := (@interpf_smart_bound _ op interp_base_type_bounds bound_base_type Cast).
  Local Notation interpf_smart_unbound := (@interpf_smart_unbound _ op interp_base_type_bounds bound_base_type Cast).

  Fixpoint wf_UnSmartArrow {var1 var2} k t1 G e_bounds input_bounds e1 e2
           (Hwf : wf G e1 e2)
           {struct t1}
    : wf G
         (@UnSmartArrow (fun t => @expr base_type_code op var1 (k t)) t1 e_bounds input_bounds e1)
         (@UnSmartArrow (fun t => @expr base_type_code op var2 (k t)) t1 e_bounds input_bounds e2).
  Proof.
    destruct t1 as [t1|s d];
      [ clear wf_UnSmartArrow
      | specialize (wf_UnSmartArrow var1 var2 (fun t => k (Arrow (bound_base_type _ (fst input_bounds)) t)) d G (e_bounds (fst input_bounds)) (snd input_bounds)) ];
      set (e1' := e1); set (e2' := e2);
        let t := match type of Hwf with wf (t:=?t) _ _ _ => t end in
        set (Tt := t) in e1, e2, Hwf;
          pose (eq_refl : Tt = t) as Ht;
          generalize (eq_refl : e1' = match Ht in (_ = y) return expr _ _ y with eq_refl => e1 end);
          generalize (eq_refl : e2' = match Ht in (_ = y) return expr _ _ y with eq_refl => e2 end);
          clearbody Ht; revert Ht;
            clearbody e1' e2'; revert e1' e2';
              clearbody Tt;
              destruct Hwf;
              intros; simpl in *; repeat subst; try discriminate;
                break_innermost_match;
                inversion_type; subst; simpl.
    { constructor; assumption. }
    { constructor; assumption. }
    { apply wf_UnSmartArrow; clear wf_UnSmartArrow.
      match goal with
      | [ |- context[match k ?x with _ => _ end] ]
        => set (kx := k x) in *
      end.
      repeat match goal with
             | [ H : context[k ?x] |- _ ]
               => change (k x) with kx in H
             | [ |- context[k ?x] ]
               => change (k x) with kx
             end.
      destruct kx;
        inversion_type; subst; simpl;
          try tauto;
          try (constructor; assumption). }
    { apply wf_UnSmartArrow; clear wf_UnSmartArrow.
      match goal with
      | [ |- context[match k ?x with _ => _ end] ]
        => set (kx := k x) in *
      end.
      repeat match goal with
             | [ H : context[k ?x] |- _ ]
               => change (k x) with kx in H
             | [ |- context[k ?x] ]
               => change (k x) with kx
             end.
      destruct kx;
        inversion_type; break_innermost_match; subst; simpl;
          try tauto;
          try (constructor; assumption). }
  Qed.

  Local Hint Resolve List.in_app_or List.in_or_app.

  Lemma wff_SmartPairf_interpf_smart_unbound var1 var2 t input_bounds x1 x2
    : wff (flatten_binding_list x1 x2)
          (SmartPairf
             (var:=var1)
             (interpf_smart_unbound input_bounds
                                    (SmartVarfMap (fun t => Var) x1)))
          (SmartPairf
             (var:=var2)
             (t:=t)
             (interpf_smart_unbound input_bounds
                                    (SmartVarfMap (fun t => Var) x2))).
  Proof.
    unfold SmartPairf, SmartVarfMap, interpf_smart_unbound; induction t;
      repeat match goal with
             | _ => progress simpl in *
             | [ |- wff _ (Cast _ _ _ _) (Cast _ _ _ _) ]
               => apply wff_Cast
             | [ |- wff _ _ _ ]
               => constructor
             | _ => solve [ auto with wf ]
             | _ => eapply wff_in_impl_Proper; [ solve [ eauto ] | ]
             | _ => intro
             end.
  Qed.

  Local Hint Resolve wff_SmartPairf_interpf_smart_unbound : wf.

  Lemma wf_smart_bound {var1 var2 t1} G e1 e2 e_bounds input_bounds
        (Hwf : wf G e1 e2)
    : wf G
         (@smart_bound var1 t1 e1 e_bounds input_bounds)
         (@smart_bound var2 t1 e2 e_bounds input_bounds).
  Proof.
    unfold SmartBound.smart_bound.
    apply wf_UnSmartArrow with (k:=fun x => x).
    apply wf_SmartAbs; intros.
    repeat constructor; auto with wf;
      try (eapply wff_in_impl_Proper; [ solve [ eauto with wf ] | ]);
      auto.
    { admit. }
    { admit. }
  Admitted.

  Lemma Wf_SmartBound {t1} e input_bounds
        (Hwf : Wf e)
    : Wf (@SmartBound t1 e input_bounds).
  Proof.
    intros var1 var2; specialize (Hwf var1 var2).
    unfold SmartBound.SmartBound.
    apply wf_smart_bound; assumption.
  Qed.
End language.
