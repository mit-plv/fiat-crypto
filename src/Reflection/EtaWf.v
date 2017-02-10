Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.WfInversion.
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
    | [ |- wf _ _ _ ] => constructor
    | _ => progress split_iff
    | _ => rewrite eq_interp_flat_type_eta_gen by assumption
    | [ H : _ |- _ ] => rewrite eq_interp_flat_type_eta_gen in H by assumption
    | [ H : appcontext[interp_flat_type_eta_gen] |- _ ]
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

      Lemma wff_exprf_eta_gen {t e1 e2} G
        : wff G (exprf_eta_gen eta (t:=t) e1) (exprf_eta_gen eta (t:=t) e2)
          <-> @wff base_type_code op var1 var2 G t e1 e2.
      Proof.
        revert G; induction e1; first [ progress invert_expr | destruct e2 ];
          t; inversion_wff_step; t.
      Qed.
    End gen_flat_type.

    (* Local *) Hint Resolve -> wff_exprf_eta_gen.
    (* Local *) Hint Resolve <- wff_exprf_eta_gen.

    Lemma wff_exprf_eta {G t e1 e2}
      : wff G (exprf_eta (t:=t) e1) (exprf_eta (t:=t) e2)
        <-> @wff base_type_code op var1 var2 G t e1 e2.
    Proof. setoid_rewrite wff_exprf_eta_gen; reflexivity. Qed.
    Lemma wff_exprf_eta' {G t e1 e2}
      : wff G (exprf_eta' (t:=t) e1) (exprf_eta' (t:=t) e2)
        <-> @wff base_type_code op var1 var2 G t e1 e2.
    Proof. setoid_rewrite wff_exprf_eta_gen; intuition. Qed.
  End with_var.
End language.
