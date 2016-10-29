(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.Inline.
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
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type interp_base_type.
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).
  Local Notation wf := (@wf base_type_code interp_base_type op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Local Hint Constructors Syntax.wff.
    Local Hint Resolve List.in_app_or List.in_or_app.

    Local Hint Constructors or.
    Local Hint Constructors Syntax.wff.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.
    Local Hint Resolve wff_SmartVar.
    Local Hint Resolve wff_SmartConst.

    Local Ltac t_fin :=
      repeat first [ intro
                   | progress inversion_sigma
                   | progress inversion_prod
                   | tauto
                   | progress subst
                   | solve [ auto with nocore
                           | eapply (@wff_SmartVarVar _ _ _ _ _ _ _ (_ * _)); auto
                           | eapply wff_SmartConst; eauto with nocore
                           | eapply wff_SmartVarVar; eauto with nocore ]
                   | progress simpl in *
                   | constructor
                   | solve [ eauto ] ].

    Lemma wff_inline_constf {t} e1 e2 G G'
             (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf t * exprf t)%type) t (x, x')) G'
                            -> wff G x x')
             (wf : wff G' e1 e2)
      : @wff var1 var2 G t (inline_constf e1) (inline_constf e2).
    Proof.
      revert dependent G; induction wf; simpl in *; intros; auto;
        specialize_by auto.
      repeat match goal with
             | [ H : context[List.In _ (_ ++ _)] |- _ ]
               => setoid_rewrite List.in_app_iff in H
             end.
      match goal with
      | [ H : _ |- _ ]
        => pose proof (IHwf _ H) as IHwf'
      end.
      destruct IHwf'; simpl in *;
        repeat constructor; auto; intros;
          match goal with
          | [ H : _ |- _ ]
            => apply H; intros; progress destruct_head' or
          end;
          t_fin.
    Qed.

    Lemma wf_inline_const {t} e1 e2 G G'
          (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf t * exprf t)%type) t (x, x')) G'
                              -> wff G x x')
          (Hwf : wf G' e1 e2)
      : @wf var1 var2 G t (inline_const e1) (inline_const e2).
    Proof.
      revert dependent G; induction Hwf; simpl; constructor; intros;
        [ eapply wff_inline_constf; eauto | ].
      match goal with
      | [ H : _ |- _ ]
        => apply H; simpl; intros; progress destruct_head' or
      end;
        inversion_sigma; inversion_prod; repeat subst; simpl.
      { constructor; left; reflexivity. }
      { eauto. }
    Qed.
  End with_var.

  Lemma WfInlineConst {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (InlineConst e).
  Proof.
    intros var1 var2.
    apply (@wf_inline_const var1 var2 t (e _) (e _) nil nil); simpl; [ tauto | ].
    apply Hwf.
  Qed.
End language.
