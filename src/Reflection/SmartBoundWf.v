Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.SmartBound.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.SmartCastWf.
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
  Local Notation interpf_smart_bound_exprf := (@interpf_smart_bound_exprf _ op interp_base_type_bounds bound_base_type Cast).
  Local Notation interpf_smart_unbound_exprf := (@interpf_smart_unbound_exprf _ op interp_base_type_bounds bound_base_type Cast).
  Local Notation bound_op := (@bound_op _ _ _ interp_op_bounds bound_base_type _ base_type_bl_transparent base_type_leb Cast genericize_op).
  Local Notation wff_SmartCast_match := (@wff_SmartCast_match _ op _ base_type_bl_transparent Cast wff_Cast).

  Local Hint Resolve List.in_or_app wff_in_impl_Proper.

  Lemma wff_bound_op
        ovar1 ovar2 G src1 dst1 src2 dst2 opc1 opc2 e1 e2 args2
        (Hwf : wff G (var1:=ovar1) (var2:=ovar2) e1 e2)
    : wff G
          (@bound_op ovar1 src1 dst1 src2 dst2 opc1 opc2 e1 args2)
          (@bound_op ovar2 src1 dst1 src2 dst2 opc1 opc2 e2 args2).
  Proof.
    unfold SmartBound.bound_op;
      repeat first [ progress break_innermost_match
                   | assumption
                   | constructor
                   | intro
                   | eapply wff_in_impl_Proper; [ eapply wff_SmartCast; eassumption | ]
                   | match goal with
                     | [ H0 : SmartCast.SmartCast _ _ _ ?x ?y = Some _, H1 : SmartCast.SmartCast _ _ _ ?x ?y = None |- _ ]
                       => let H := fresh in
                          refine (let H := wff_SmartCast_match x y in _);
                          erewrite H0, H1 in H; exfalso; exact H
                     end
                   | solve [ auto ] ].
  Qed.

  Local Hint Resolve List.in_app_or List.in_or_app.

  Lemma wff_SmartPairf_interpf_smart_unbound_exprf var1 var2 t input_bounds x1 x2
    : wff (flatten_binding_list x1 x2)
          (SmartPairf
             (var:=var1)
             (interpf_smart_unbound_exprf input_bounds
                                          (SmartVarfMap (fun t => Var) x1)))
          (SmartPairf
             (var:=var2)
             (t:=t)
             (interpf_smart_unbound_exprf input_bounds
                                          (SmartVarfMap (fun t => Var) x2))).
  Proof.
    clear -wff_Cast.
    unfold SmartPairf, SmartVarfMap, interpf_smart_unbound_exprf; induction t;
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

  Local Hint Resolve wff_SmartPairf_interpf_smart_unbound_exprf : wf.

  Lemma wff_SmartPairf_interpf_smart_bound_exprf var1 var2 t x1 x2 output_bounds
    : wff (flatten_binding_list x1 x2)
          (SmartPairf
             (var:=var1)
             (interpf_smart_bound_exprf (t:=t) x1 output_bounds))
          (SmartPairf
             (var:=var2)
             (interpf_smart_bound_exprf x2 output_bounds)).
  Proof.
    clear -wff_Cast.
    unfold SmartPairf, SmartVarfMap, interpf_smart_bound_exprf; induction t;
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

  Local Hint Resolve wff_SmartPairf_interpf_smart_bound_exprf : wf.

  Lemma wf_smart_bound {var1 var2 t1} e1 e2 e_bounds input_bounds
        (Hwf : wf e1 e2)
    : wf (@smart_bound var1 t1 e1 e_bounds input_bounds)
         (@smart_bound var2 t1 e2 e_bounds input_bounds).
  Proof.
    clear -wff_Cast Hwf.
    destruct Hwf; unfold SmartBound.smart_bound.
    repeat constructor; auto with wf; intros;
      try (eapply wff_in_impl_Proper; [ solve [ eauto with wf ] | ]);
      auto.
  Qed.

  Lemma Wf_SmartBound {t1} e input_bounds
        (Hwf : Wf e)
    : Wf (@SmartBound t1 e input_bounds).
  Proof.
    intros var1 var2; specialize (Hwf var1 var2).
    unfold SmartBound.SmartBound.
    apply wf_smart_bound; assumption.
  Qed.
End language.

Hint Resolve Wf_SmartBound wff_bound_op : wf.
