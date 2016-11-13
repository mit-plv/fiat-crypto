Require Import Crypto.SpecificGen.GF5211_32Reflective.CommonBinOp.

Definition rsubZ_sig : rexpr_binop_sig sub. Proof. reify_sig. Defined.
Definition rsubW := Eval vm_compute in rword_of_Z rsubZ_sig.
Lemma rsubW_correct_and_bounded_gen : correct_and_bounded_genT rsubW rsubZ_sig.
Proof. rexpr_correct. Qed.
Definition rsub_output_bounds := Eval vm_compute in compute_bounds rsubW ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Sub", compute_bounds_for_display rsubW ExprBinOp_bounds).
Compute ("Sub overflows? ", sanity_compute rsubW ExprBinOp_bounds).
Compute ("Sub overflows (error if it does)? ", sanity_check rsubW ExprBinOp_bounds).
