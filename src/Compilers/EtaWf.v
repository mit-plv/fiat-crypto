Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation exprf := (@exprf base_type_code op).

  Local Ltac t_step :=
    match goal with
    | _ => intro
    | _ => progress subst
    | _ => progress destruct_head' sig
    | _ => progress destruct_head' and
    | _ => progress simpl in *
    | _ => progress inversion_expr
    | _ => progress destruct_head' @expr
    | _ => progress invert_expr_step
    | [ |- iff _ _ ] => split
    | [ |- wf _ _ ] => constructor
    | _ => progress split_iff
    | _ => rewrite eq_interp_flat_type_eta_gen by assumption
    | [ H : _ |- _ ] => rewrite eq_interp_flat_type_eta_gen in H by assumption
    | [ H : context[interp_flat_type_eta_gen] |- _ ]
      => setoid_rewrite eq_interp_flat_type_eta_gen in H; [ | assumption.. ]
    | _ => progress break_match
    | [ H : wff _ _ _ |- _ ] => solve [ inversion H ]
    | [ |- wff _ _ _ ] => constructor
    | _ => solve [ auto | congruence | tauto ]
    end.
  Local Ltac t := repeat t_step.

  Local Hint Constructors wff.

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.
    Section gen_flat_type.
      Context (eta : forall {A B}, A * B -> A * B)
              (eq_eta : forall A B x, @eta A B x = x).
      Section gen_type.
        Context (exprf_eta1 : forall {t} (e : exprf t), exprf t)
                (exprf_eta2 : forall {t} (e : exprf t), exprf t)
                (wff_exprf_eta : forall G t e1 e2, @wff _ _ var1 var2 G t e1 e2
                                                   <-> @wff _ _ var1 var2 G t (@exprf_eta1 t e1) (@exprf_eta2 t e2)).
        Lemma wf_expr_eta_gen {t e1 e2}
          : wf (expr_eta_gen eta exprf_eta1 (t:=t) e1)
               (expr_eta_gen eta exprf_eta2 (t:=t) e2)
            <-> wf e1 e2.
        Proof using Type*. unfold expr_eta_gen; t; inversion_wf_step; t. Qed.
      End gen_type.

      Lemma wff_exprf_eta_gen {t e1 e2} G
        : wff G (exprf_eta_gen eta (t:=t) e1) (exprf_eta_gen eta (t:=t) e2)
          <-> @wff base_type_code op var1 var2 G t e1 e2.
      Proof using eq_eta.
        revert G; induction e1; first [ progress invert_expr | destruct e2 ];
          t; inversion_wf_step; t.
      Qed.
    End gen_flat_type.

    (* Local *) Hint Resolve -> wff_exprf_eta_gen.
    (* Local *) Hint Resolve <- wff_exprf_eta_gen.

    Lemma wff_exprf_eta {G t e1 e2}
      : wff G (exprf_eta (t:=t) e1) (exprf_eta (t:=t) e2)
        <-> @wff base_type_code op var1 var2 G t e1 e2.
    Proof using Type. setoid_rewrite wff_exprf_eta_gen; reflexivity. Qed.
    Lemma wff_exprf_eta' {G t e1 e2}
      : wff G (exprf_eta' (t:=t) e1) (exprf_eta' (t:=t) e2)
        <-> @wff base_type_code op var1 var2 G t e1 e2.
    Proof using Type. setoid_rewrite wff_exprf_eta_gen; intuition. Qed.
    Lemma wf_expr_eta {t e1 e2}
      : wf (expr_eta (t:=t) e1) (expr_eta (t:=t) e2)
        <-> @wf base_type_code op var1 var2 t e1 e2.
    Proof using Type.
      unfold expr_eta, exprf_eta.
      setoid_rewrite wf_expr_eta_gen; intuition (solve [ eapply wff_exprf_eta_gen; [ | eassumption ]; intuition ] || eauto).
    Qed.
    Lemma wf_expr_eta' {t e1 e2}
      : wf (expr_eta' (t:=t) e1) (expr_eta' (t:=t) e2)
        <-> @wf base_type_code op var1 var2 t e1 e2.
    Proof using Type.
      unfold expr_eta', exprf_eta'.
      setoid_rewrite wf_expr_eta_gen; intuition (solve [ eapply wff_exprf_eta_gen; [ | eassumption ]; intuition ] || eauto).
    Qed.
  End with_var.

  Lemma Wf_ExprEtaGen
        (eta : forall {A B}, A * B -> A * B)
        (eq_eta : forall A B x, @eta A B x = x)
        {t e}
    : Wf (ExprEtaGen (@eta) e) <-> @Wf base_type_code op t e.
  Proof using Type.
    split; intros H var1 var2; specialize (H var1 var2);
      revert H; eapply wf_expr_eta_gen; try eassumption; intros;
        symmetry; apply wff_exprf_eta_gen;
          auto.
  Qed.
  Lemma Wf_ExprEta_iff
        {t e}
    : Wf (ExprEta e) <-> @Wf base_type_code op t e.
  Proof using Type.
    unfold Wf; setoid_rewrite wf_expr_eta; reflexivity.
  Qed.
  Lemma Wf_ExprEta'_iff
        {t e}
    : Wf (ExprEta' e) <-> @Wf base_type_code op t e.
  Proof using Type.
    unfold Wf; setoid_rewrite wf_expr_eta'; reflexivity.
  Qed.
  Definition Wf_ExprEta {t e} : Wf e -> Wf (ExprEta e) := proj2 (@Wf_ExprEta_iff t e).
  Definition Wf_ExprEta' {t e} : Wf e -> Wf (ExprEta' e) := proj2 (@Wf_ExprEta'_iff t e).
End language.

Hint Resolve Wf_ExprEta Wf_ExprEta' : wf.
