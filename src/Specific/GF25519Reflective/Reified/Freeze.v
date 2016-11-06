Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rfreezeZ_sig : rexpr_unop_sig freeze. Proof. reify_sig. Defined.
Definition rfreezeW := Eval vm_compute in rword_of_Z rfreezeZ_sig.
Lemma rfreezeW_correct_and_bounded_gen : correct_and_bounded_genT rfreezeW rfreezeZ_sig.
Proof. rexpr_correct. Qed.
Definition rfreeze_output_bounds := Eval vm_compute in compute_bounds rfreezeW ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Axiom admit : forall {T}, T.
(** XXX TODO: Fix bounds analysis on freeze *)
Definition rfreezeW_correct_and_bounded
  := ExprUnOp_correct_and_bounded
       rfreezeW freeze rfreezeZ_sig rfreezeW_correct_and_bounded_gen
       admit admit.

Local Open Scope string_scope.
Compute ("Freeze", compute_bounds_for_display rfreezeW ExprUnOp_bounds).
(*Compute ("Freeze overflows? ", sanity_check rfreezeW ExprUnOp_bounds).*)
