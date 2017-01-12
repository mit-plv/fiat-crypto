Require Import Crypto.SpecificGen.GF5211_32Reflective.CommonUnOp.

Definition rprefreezeZ_sig : rexpr_unop_sig prefreeze. Proof. reify_sig. Defined.
Definition rprefreezeW := Eval vm_compute in rword_of_Z rprefreezeZ_sig.
Lemma rprefreezeW_correct_and_bounded_gen : correct_and_bounded_genT rprefreezeW rprefreezeZ_sig.
Proof. rexpr_correct. Qed.
Definition rprefreeze_output_bounds := Eval vm_compute in compute_bounds rprefreezeW ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rprefreezeW_correct_and_bounded
  := ExprUnOp_correct_and_bounded
       rprefreezeW prefreeze rprefreezeZ_sig rprefreezeW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("PreFreeze", compute_bounds_for_display rprefreezeW ExprUnOp_bounds).
Compute ("PreFreeze overflows? ", sanity_compute rprefreezeW ExprUnOp_bounds).
Compute ("PreFreeze overflows (error if it does)? ", sanity_check rprefreezeW ExprUnOp_bounds).
