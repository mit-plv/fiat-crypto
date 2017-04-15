(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.CommonSubexpressionEliminationInterp.
Require Import Crypto.Compilers.Z.CommonSubexpressionElimination.

Lemma InterpCSE_gen inline_symbolic_expr_in_lookup t (e : Expr _ _ t) prefix
      (Hwf : Wf e)
  : forall x, Interp interp_op (@CSE_gen inline_symbolic_expr_in_lookup t e prefix) x = Interp interp_op e x.
Proof.
  apply InterpCSE;
    auto using internal_base_type_dec_bl, internal_base_type_dec_lb, internal_symbolic_op_dec_bl, internal_symbolic_op_dec_lb, denote_symbolic_op.
Qed.

Lemma InterpCSE inline_symbolic_expr_in_lookup t (e : Expr _ _ t) (Hwf : Wf e)
  : forall x, Interp interp_op (@CSE inline_symbolic_expr_in_lookup t e) x = Interp interp_op e x.
Proof.
  apply InterpCSE_gen; auto.
Qed.

Hint Rewrite @InterpCSE using solve_wf_side_condition : reflective_interp.
