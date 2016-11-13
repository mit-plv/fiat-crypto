Require Import Crypto.SpecificGen.GF25519_64Reflective.CommonBinOp.

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.
Definition raddW := Eval vm_compute in rword_of_Z raddZ_sig.
Lemma raddW_correct_and_bounded_gen : correct_and_bounded_genT raddW raddZ_sig.
Proof. rexpr_correct. Qed.
Definition radd_output_bounds := Eval vm_compute in compute_bounds raddW ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Add", compute_bounds_for_display raddW ExprBinOp_bounds).
Compute ("Add overflows? ", sanity_compute raddW ExprBinOp_bounds).
Compute ("Add overflows (error if it does)? ", sanity_check raddW ExprBinOp_bounds).
