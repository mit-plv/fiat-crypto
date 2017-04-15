(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.CommonSubexpressionEliminationWf.
Require Import Crypto.Compilers.Z.CommonSubexpressionElimination.

Lemma Wf_CSE_gen inline_symbolic_expr_in_lookup t (e : Expr _ _ t)
      prefix
      (Hlen : forall var1 var2, length (prefix var1) = length (prefix var2))
      (Hprefix : forall var1 var2 n t1 t2 e1 e2,
          List.nth_error (prefix var1) n = Some (existT _ t1 e1)
          -> List.nth_error (prefix var2) n = Some (existT _ t2 e2)
          -> exists pf : t1 = t2, wff nil (eq_rect _ (@exprf _ _ _) e1 _ pf) e2)
      (Hwf : Wf e)
  : Wf (@CSE_gen inline_symbolic_expr_in_lookup t e prefix).
Proof.
  apply Wf_CSE; auto using internal_base_type_dec_bl, internal_base_type_dec_lb, internal_symbolic_op_dec_bl, internal_symbolic_op_dec_lb.
Qed.

Lemma Wf_CSE inline_symbolic_expr_in_lookup t (e : Expr _ _ t)
      (Hwf : Wf e)
  : Wf (@CSE inline_symbolic_expr_in_lookup t e).
Proof.
  apply Wf_CSE_gen; simpl; auto.
  { destruct n; simpl; try congruence. }
Qed.

Hint Resolve Wf_CSE : wf.
