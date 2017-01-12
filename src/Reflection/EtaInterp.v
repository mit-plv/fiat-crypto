Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.

  Local Notation exprf := (@exprf base_type_code op interp_base_type).

  Local Ltac t_step :=
    match goal with
    | _ => reflexivity
    | _ => progress simpl in *
    | _ => intro
    | _ => progress break_match
    | _ => progress destruct_head prod
    | _ => progress cbv [LetIn.Let_In]
    | [ H : _ |- _ ] => rewrite H
    | _ => progress autorewrite with core
    | [ H : forall A B x, ?f A B x = x, H' : context[?f _ _ _] |- _ ]
      => rewrite H in H'
    | _ => progress unfold interp_flat_type_eta, interp_flat_type_eta', exprf_eta, exprf_eta', expr_eta, expr_eta'
    end.
  Local Ltac t := repeat t_step.

  Section gen_flat_type.
    Context (eta : forall {A B}, A * B -> A * B)
            (eq_eta : forall A B x, @eta A B x = x).
    Lemma eq_interp_flat_type_eta_gen {var t T f} x
      : @interp_flat_type_eta_gen base_type_code var eta t T f x = f x.
    Proof. induction t; t. Qed.

    (* Local *) Hint Rewrite @eq_interp_flat_type_eta_gen.

    Section gen_type.
      Context (exprf_eta : forall {t} (e : exprf t), exprf t)
              (eq_interp_exprf_eta : forall t e, interpf (@interp_op) (@exprf_eta t e) = interpf (@interp_op) e).
      Lemma interp_expr_eta_gen {t e}
        : forall x,
          interp (@interp_op) (expr_eta_gen eta exprf_eta (t:=t) e) x = interp (@interp_op) e x.
      Proof. t. Qed.
    End gen_type.
    (* Local *) Hint Rewrite @interp_expr_eta_gen.

    Lemma interpf_exprf_eta_gen {t e}
      : interpf (@interp_op) (exprf_eta_gen eta (t:=t) e) = interpf (@interp_op) e.
    Proof. induction e; t. Qed.

    Lemma InterpExprEtaGen {t e}
      : forall x, Interp (@interp_op) (ExprEtaGen eta (t:=t) e) x = Interp (@interp_op) e x.
    Proof. apply interp_expr_eta_gen; intros; apply interpf_exprf_eta_gen. Qed.
  End gen_flat_type.
  (* Local *) Hint Rewrite @eq_interp_flat_type_eta_gen.
  (* Local *) Hint Rewrite @interp_expr_eta_gen.
  (* Local *) Hint Rewrite @interpf_exprf_eta_gen.

  Lemma eq_interp_flat_type_eta {var t T f} x
    : @interp_flat_type_eta base_type_code var t T f x = f x.
  Proof. t. Qed.
  (* Local *) Hint Rewrite @eq_interp_flat_type_eta.
  Lemma eq_interp_flat_type_eta' {var t T f} x
    : @interp_flat_type_eta' base_type_code var t T f x = f x.
  Proof. t. Qed.
  (* Local *) Hint Rewrite @eq_interp_flat_type_eta'.
  Lemma interpf_exprf_eta {t e}
    : interpf (@interp_op) (exprf_eta (t:=t) e) = interpf (@interp_op) e.
  Proof. t. Qed.
  (* Local *) Hint Rewrite @interpf_exprf_eta.
  Lemma interpf_exprf_eta' {t e}
    : interpf (@interp_op) (exprf_eta' (t:=t) e) = interpf (@interp_op) e.
  Proof. t. Qed.
  (* Local *) Hint Rewrite @interpf_exprf_eta'.
  Lemma interp_expr_eta {t e}
    : forall x, interp (@interp_op) (expr_eta (t:=t) e) x = interp (@interp_op) e x.
  Proof. t. Qed.
  Lemma interp_expr_eta' {t e}
    : forall x, interp (@interp_op) (expr_eta' (t:=t) e) x = interp (@interp_op) e x.
  Proof. t. Qed.
  Lemma InterpExprEta {t e}
    : forall x, Interp (@interp_op) (ExprEta (t:=t) e) x = Interp (@interp_op) e x.
  Proof. apply interp_expr_eta. Qed.
  Lemma InterpExprEta' {t e}
    : forall x, Interp (@interp_op) (ExprEta' (t:=t) e) x = Interp (@interp_op) e x.
  Proof. apply interp_expr_eta'. Qed.
End language.
