Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Rewriter.
Require Import Crypto.Util.Tactics.RewriteHyp.

Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op interp_base_type).
  Local Notation expr := (@expr base_type_code op interp_base_type).
  Local Notation Expr := (@Expr base_type_code op).

  Section specialized.
    Context {rewrite_op_expr : forall src dst (opc : op src dst), exprf src -> exprf dst}
            (Hrewrite : forall src dst opc args,
                interpf interp_op (rewrite_op_expr src dst opc args)
                = interp_op _ _ opc (interpf interp_op args)).

    Lemma interpf_rewrite_opf {t} (e : exprf t)
      : interpf interp_op (rewrite_opf rewrite_op_expr e) = interpf interp_op e.
    Proof.
      induction e; simpl; unfold LetIn.Let_In; rewrite_hyp ?*; reflexivity.
    Qed.

    Lemma interp_rewrite_op {t} (e : expr t)
      : forall x, interp interp_op (rewrite_op rewrite_op_expr e) x = interp interp_op e x.
    Proof.
      destruct e; intro x; apply interpf_rewrite_opf.
    Qed.
  End specialized.

  Lemma InterpRewriteOp
        {rewrite_op_expr}
        (Hrewrite : forall src dst opc args,
            interpf interp_op (rewrite_op_expr interp_base_type src dst opc args)
            = interp_op _ _ opc (interpf interp_op args))
        {t} (e : Expr t)
    : forall x, Interp interp_op (RewriteOp rewrite_op_expr e) x = Interp interp_op e x.
  Proof.
    apply interp_rewrite_op; assumption.
  Qed.
End language.
