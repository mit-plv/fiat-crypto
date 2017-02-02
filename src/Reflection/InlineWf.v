(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Util.Tactics.SpecializeBy Crypto.Util.Tactics.DestructHead Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation Tbase := (@Tbase base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op).
  Local Notation wf := (@wf base_type_code op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Local Hint Constructors Wf.wff.
    Local Hint Resolve List.in_app_or List.in_or_app.

    Local Hint Constructors or.
    Local Hint Constructors Wf.wff.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.
    Local Hint Resolve wff_SmartVarf.
    Local Hint Resolve wff_SmartVarVarf.

    Local Ltac t_fin :=
      repeat first [ intro
                   | progress inversion_sigma
                   | progress inversion_prod
                   | tauto
                   | progress subst
                   | solve [ auto with nocore
                           | eapply (@wff_SmartVarVarf _ _ _ _ _ _ (_ * _)); auto
                           | eapply wff_SmartVarVarf; eauto with nocore ]
                   | progress simpl in *
                   | constructor
                   | solve [ eauto ] ].

    Lemma wff_inline_constf is_const {t} e1 e2 G G'
             (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x, x')) G'
                            -> wff G x x')
             (wf : wff G' e1 e2)
      : @wff var1 var2 G t (inline_constf is_const e1) (inline_constf is_const e2).
    Proof.
      revert dependent G; induction wf; simpl in *; intros; auto;
        specialize_by auto; unfold postprocess_for_const.
      repeat match goal with
             | [ H : context[List.In _ (_ ++ _)] |- _ ]
               => setoid_rewrite List.in_app_iff in H
             end.
      match goal with
      | [ H : _ |- _ ]
        => pose proof (IHwf _ H) as IHwf'
      end.
      generalize dependent (inline_constf is_const e1); generalize dependent (inline_constf is_const e1'); intros.
      destruct IHwf'; simpl in *;
        try match goal with |- context[@is_const ?x ?y ?z] => is_var y; destruct (@is_const x y z), y end;
        repeat constructor; auto; intros;
          match goal with
          | [ H : _ |- _ ]
            => apply H; intros; progress destruct_head_hnf' or
          end;
          t_fin.
    Qed.

    Lemma wf_inline_const is_const {t} e1 e2 G G'
          (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x, x')) G'
                              -> wff G x x')
          (Hwf : wf G' e1 e2)
      : @wf var1 var2 G t (inline_const is_const e1) (inline_const is_const e2).
    Proof.
      revert dependent G; induction Hwf; simpl; constructor; intros;
        [ eapply (wff_inline_constf is_const); [ | solve [ eauto ] ] | ];
        match goal with
        | [ H : _ |- _ ]
          => apply H; simpl; intros; progress destruct_head' or
        end;
        inversion_sigma; inversion_prod; repeat subst; simpl.
      { constructor; left; reflexivity. }
      { eauto. }
    Qed.
  End with_var.

  Lemma Wf_InlineConst is_const {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (InlineConst is_const e).
  Proof.
    intros var1 var2.
    apply (@wf_inline_const var1 var2 is_const t (e _) (e _) nil nil); simpl; [ tauto | ].
    apply Hwf.
  Qed.
End language.

Hint Resolve Wf_InlineConst : wf.
