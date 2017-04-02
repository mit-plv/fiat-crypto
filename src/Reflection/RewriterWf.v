Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Reflection.Rewriter.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation wff := (@wff base_type_code op).
  Local Notation wf := (@wf base_type_code op).
  Local Notation Wf := (@Wf base_type_code op).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}
            {rewrite_op_expr1 : forall src dst (opc : op src dst),
                exprf (var:=var1) src -> exprf (var:=var1) dst}
            {rewrite_op_expr2 : forall src dst (opc : op src dst),
                exprf (var:=var2) src -> exprf (var:=var2) dst}
            (Hrewrite_wf : forall G src dst opc args1 args2,
                wff G args1 args2
                -> wff G
                       (rewrite_op_expr1 src dst opc args1)
                       (rewrite_op_expr2 src dst opc args2)).

    Lemma wff_rewrite_opf {t} G (e1 : @exprf var1 t) (e2 : @exprf var2 t)
          (Hwf : wff G e1 e2)
      : wff G (rewrite_opf rewrite_op_expr1 e1) (rewrite_opf rewrite_op_expr2 e2).
    Proof.
      induction Hwf; simpl; try constructor; auto.
    Qed.

    Lemma wf_rewrite_opf {t} (e1 : @expr var1 t) (e2 : @expr var2 t)
          (Hwf : wf e1 e2)
      : wf (rewrite_op rewrite_op_expr1 e1) (rewrite_op rewrite_op_expr2 e2).
    Proof.
      destruct Hwf; simpl; constructor; intros; apply wff_rewrite_opf; auto.
    Qed.
  End with_var.

  Lemma Wf_RewriteOp
        {rewrite_op_expr}
        (Hrewrite_wff : forall var1 var2 G src dst opc args1 args2,
            wff G args1 args2
            -> wff G
                   (rewrite_op_expr var1 src dst opc args1)
                   (rewrite_op_expr var2 src dst opc args2))
        {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (RewriteOp rewrite_op_expr e).
  Proof.
    intros var1 var2; apply wf_rewrite_opf; auto.
  Qed.
End language.

Hint Resolve Wf_RewriteOp : wf.
