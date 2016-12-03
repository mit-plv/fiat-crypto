Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.
    Local Hint Constructors Syntax.wff.

    Lemma wff_app' {g G0 G1 t e1 e2}
          (wf : @wff var1 var2 (G0 ++ G1) t e1 e2)
      : wff (G0 ++ g ++ G1) e1 e2.
    Proof.
      rewrite !List.app_assoc.
      revert wf; remember (G0 ++ G1)%list as G eqn:?; intro wf.
      revert dependent G0. revert dependent G1.
      induction wf; simpl in *; constructor; simpl; eauto.
      { subst; rewrite !List.in_app_iff in *; intuition. }
      { intros; subst.
        rewrite !List.app_assoc; eauto using List.app_assoc. }
    Qed.

    Lemma wff_app_pre {g G t e1 e2}
          (wf : @wff var1 var2 G t e1 e2)
      : wff (g ++ G) e1 e2.
    Proof.
      apply (@wff_app' _ nil); assumption.
    Qed.

    Lemma wff_app_post {g G t e1 e2}
          (wf : @wff var1 var2 G t e1 e2)
      : wff (G ++ g) e1 e2.
    Proof.
      pose proof (@wff_app' g G nil t e1 e2) as H.
      rewrite !List.app_nil_r in *; auto.
    Qed.

    Lemma wff_in_impl_Proper G0 G1 {t} e1 e2
      : @wff var1 var2 G0 t e1 e2
        -> (forall x, List.In x G0 -> List.In x G1)
        -> @wff var1 var2 G1 t e1 e2.
    Proof.
      intro wf; revert G1; induction wf;
        repeat match goal with
               | _ => setoid_rewrite List.in_app_iff
               | _ => progress intros
               | _ => progress simpl in *
               | [ |- wff _ _ _ ] => constructor
               | [ H : _ |- _ ] => apply H
               | _ => solve [ intuition eauto ]
               end.
    Qed.

    Local Hint Resolve List.in_app_or List.in_or_app.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.

    Lemma wff_SmartVarf {t} x1 x2
      : @wff var1 var2 (flatten_binding_list base_type_code x1 x2) t (SmartVarf x1) (SmartVarf x2).
    Proof.
      unfold SmartVarf.
      induction t; simpl; constructor; eauto.
    Qed.

    Local Hint Resolve wff_SmartVarf.

    Lemma wff_Const_eta G {A B} v1 v2
      : @wff var1 var2 G (Prod A B) (Const v1) (Const v2)
        -> (@wff var1 var2 G A (Const (fst v1)) (Const (fst v2))
           /\ @wff var1 var2 G B (Const (snd v1)) (Const (snd v2))).
    Proof.
      intro wf.
      assert (H : Some v1 = Some v2).
      { refine match wf in @Syntax.wff _ _ _ _ _ G t e1 e2 return invert_Const e1 = invert_Const e2 with
               | WfConst _ _ _ => eq_refl
               | _ => eq_refl
               end. }
      inversion H; subst; repeat constructor.
    Qed.

    Definition wff_Const_eta_fst G {A B} v1 v2 H
      := proj1 (@wff_Const_eta G A B v1 v2 H).
    Definition wff_Const_eta_snd G {A B} v1 v2 H
      := proj2 (@wff_Const_eta G A B v1 v2 H).

    Local Hint Resolve wff_Const_eta_fst wff_Const_eta_snd.

    Lemma wff_SmartConstf G {t t'} v1 v2 x1 x2
          (Hin : List.In (existT (fun t : base_type_code => (@exprf var1 t * @exprf var2 t)%type) t (x1, x2))
                         (flatten_binding_list base_type_code (SmartConstf v1) (SmartConstf v2)))
          (Hwf : @wff var1 var2 G t' (Const v1) (Const v2))
      : @wff var1 var2 G t x1 x2.
    Proof.
      induction t'. simpl in *.
      { intuition (inversion_sigma; inversion_prod; subst; eauto). }
      { unfold SmartConstf in *; simpl in *.
        apply List.in_app_iff in Hin.
        intuition (inversion_sigma; inversion_prod; subst; eauto). }
    Qed.

    Local Hint Resolve wff_SmartConstf.

    Lemma wff_SmartVarVarf G {t t'} v1 v2 x1 x2
          (Hin : List.In (existT (fun t : base_type_code => (exprf t * exprf t)%type) t (x1, x2))
                          (flatten_binding_list base_type_code (SmartVarVarf v1) (SmartVarVarf v2)))
      : @wff var1 var2 (flatten_binding_list base_type_code (t:=t') v1 v2 ++ G) t x1 x2.
    Proof.
      revert dependent G; induction t'; intros. simpl in *.
      { intuition (inversion_sigma; inversion_prod; subst; simpl; eauto).
        constructor; eauto. }
      { unfold SmartVarVarf in *; simpl in *.
        apply List.in_app_iff in Hin.
        intuition (inversion_sigma; inversion_prod; subst; eauto).
        { rewrite <- !List.app_assoc; eauto. } }
    Qed.
  End with_var.
End language.
