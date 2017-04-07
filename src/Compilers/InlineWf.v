(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.Inline.
Require Import Crypto.Util.Tactics.SpecializeBy Crypto.Util.Tactics.DestructHead Crypto.Util.Sigma Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.

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

  Local Notation wff_inline_directive G x y :=
    (wff G (exprf_of_inline_directive x) (exprf_of_inline_directive y)
     /\ (fun x' y'
         => match x', y' with
            | default_inline _ _, default_inline _ _
            | no_inline _ _, no_inline _ _
            | inline _ _, inline _ _
              => True
            | default_inline _ _, _
            | no_inline _ _, _
            | inline _ _, _
              => False
            end) x y).


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

    Local Ltac invert_inline_directive' i :=
      preinvert_one_type i;
      intros ? i;
      destruct i;
      try exact I.
    Local Ltac invert_inline_directive :=
      match goal with
      | [ i : inline_directive _ |- _ ] => invert_inline_directive' i
      end.

    (** XXX TODO: Clean up this proof *)
    Lemma wff_inline_const_genf postprocess1 postprocess2 {t} e1 e2 G G'
             (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x, x')) G'
                                 -> wff G x x')
             (wf : wff G' e1 e2)
             (wf_postprocess : forall G t e1 e2,
                 wff G e1 e2
                 -> wff_inline_directive G (postprocess1 t e1) (postprocess2 t e2))
      : @wff var1 var2 G t (inline_const_genf postprocess1 e1) (inline_const_genf postprocess2 e2).
    Proof using Type.
      revert dependent G; induction wf; simpl in *; auto; intros; [].
      repeat match goal with
             | [ H : context[List.In _ (_ ++ _)] |- _ ]
               => setoid_rewrite List.in_app_iff in H
             | [ |- context[postprocess1 ?t ?e1] ]
               => match goal with
                  | [ |- context[postprocess2 t ?e2] ]
                    => specialize (fun G => wf_postprocess G t e1 e2);
                         generalize dependent (postprocess1 t e1);
                         generalize dependent (postprocess2 t e2)
                  end
             | _ => intro
             end.
      repeat match goal with
             | [ H : forall G : list _, _ |- wff ?G' _ _ ]
               => unique pose proof (H G')
             | [ H : forall x y (G : list _), _ |- wff ?G' _ _ ]
               => unique pose proof (fun x y => H x y G')
             | [ H : forall x1 x2, (forall t x x', _ \/ List.In _ ?G -> wff ?G0 x x') -> _,
                   H' : forall t1 x1 x1', List.In _ ?G -> wff ?G0 x1 x1' |- _ ]
               => unique pose proof (fun x1 x2 f => H x1 x2 (fun t x x' pf => match pf with or_introl pf => f t x x' pf | or_intror pf => H' t x x' pf end))
             end.
      repeat match goal with
             | _ => exact I
             | [ H : forall x1 : unit, _ |- _ ] => specialize (H tt)
             | [ H : False |- _ ] => exfalso; assumption
             | _ => progress subst
             | _ => progress inversion_sigma
             | _ => progress inversion_prod
             | _ => progress destruct_head' and
             | _ => inversion_wf_step; progress subst
             | _ => progress specialize_by_assumption
             | _ => progress break_match
             | _ => progress invert_inline_directive
             | [ |- context[match ?e with _ => _ end] ]
               => invert_one_expr e
             | _ => progress destruct_head' or
             | _ => progress simpl in *
             | _ => intro
             | _ => progress split_and
             | [ H : wff _ TT _ |- _ ] => solve [ inversion H ]
             | [ H : wff _ (Var _ _) _ |- _ ] => solve [ inversion H ]
             | [ H : wff _ (Op _ _) _ |- _ ] => solve [ inversion H ]
             | [ H : wff _ (LetIn _ _) _ |- _ ] => solve [ inversion H ]
             | [ H : wff _ (Pair _ _) _ |- _ ] => solve [ inversion H ]
             end;
        repeat first [ progress specialize_by tauto
                     | progress specialize_by auto
                     | solve [ auto ] ];
        try (constructor; auto; intros).
      { match goal with H : _ |- _ => apply H end.
        intros; destruct_head or; t_fin. }
      { match goal with H : _ |- _ => apply H end.
        intros; destruct_head or; t_fin. }
      { match goal with H : _ |- _ => apply H end.
        intros; destruct_head or; t_fin. }
      { match goal with H : _ |- _ => apply H end.
        intros; destruct_head' or; t_fin. }
      { match goal with H : _ |- _ => apply H end.
        intros; destruct_head or; t_fin. }
      { match goal with H : _ |- _ => apply H end.
        intros; destruct_head or; t_fin. }
    Qed.

    Lemma wff_postprocess_for_const is_const G t
          (e1 : @exprf var1 t)
          (e2 : @exprf var2 t)
          (Hwf : wff G e1 e2)
      : wff_inline_directive G (postprocess_for_const is_const t e1) (postprocess_for_const is_const t e2).
    Proof using Type.
      destruct e1; unfold postprocess_for_const;
        repeat first [ progress subst
                     | intro
                     | progress destruct_head' sig
                     | progress destruct_head' and
                     | progress inversion_sigma
                     | progress inversion_option
                     | progress inversion_prod
                     | progress destruct_head' False
                     | progress simpl in *
                     | progress invert_expr
                     | progress inversion_wf
                     | progress break_innermost_match_step
                     | discriminate
                     | congruence
                     | solve [ auto ] ].
    Qed.

    Local Hint Resolve wff_postprocess_for_const.

    Lemma wff_inline_constf is_const {t} e1 e2 G G'
             (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x, x')) G'
                            -> wff G x x')
             (wf : wff G' e1 e2)
      : @wff var1 var2 G t (inline_constf is_const e1) (inline_constf is_const e2).
    Proof using Type. eapply wff_inline_const_genf; eauto. Qed.

    Lemma wf_inline_const_gen postprocess1 postprocess2 {t} e1 e2
          (Hwf : wf e1 e2)
          (wf_postprocess : forall G t e1 e2,
              wff G e1 e2
              -> wff_inline_directive G (postprocess1 t e1) (postprocess2 t e2))
      : @wf var1 var2 t (inline_const_gen postprocess1 e1) (inline_const_gen postprocess2 e2).
    Proof using Type.
      destruct Hwf; constructor; intros.
      eapply wff_inline_const_genf; eauto using wff_SmartVarVarf_nil.
    Qed.

    Lemma wf_inline_const is_const {t} e1 e2
          (Hwf : wf e1 e2)
      : @wf var1 var2 t (inline_const is_const e1) (inline_const is_const e2).
    Proof using Type. eapply wf_inline_const_gen; eauto. Qed.
  End with_var.

  Lemma Wf_InlineConstGen postprocess {t} (e : Expr t)
        (Hwf : Wf e)
        (Hpostprocess : forall var1 var2 G t e1 e2,
            wff G e1 e2
            -> wff_inline_directive G (postprocess var1 t e1) (postprocess var2 t e2))
    : Wf (InlineConstGen postprocess e).
  Proof using Type.
    intros var1 var2.
    apply (@wf_inline_const_gen var1 var2 (postprocess _) (postprocess _) t (e _) (e _)); simpl; auto.
  Qed.

  Lemma Wf_InlineConst is_const {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (InlineConst is_const e).
  Proof using Type.
    intros var1 var2.
    apply (@wf_inline_const var1 var2 is_const t (e _) (e _)); simpl.
    apply Hwf.
  Qed.
End language.

Hint Resolve Wf_InlineConstGen Wf_InlineConst : wf.
