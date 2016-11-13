Require Import Crypto.SpecificGen.GF41417_32Reflective.CommonUnOp.

Definition roppZ_sig : rexpr_unop_sig opp. Proof. reify_sig. Defined.
Definition roppW := Eval vm_compute in rword_of_Z roppZ_sig.
Lemma roppW_correct_and_bounded_gen : correct_and_bounded_genT roppW roppZ_sig.
Proof. rexpr_correct. Qed.
Definition ropp_output_bounds := Eval vm_compute in compute_bounds roppW ExprUnOp_bounds.

Local Open Scope string_scope.
Compute ("Opp", compute_bounds_for_display roppW ExprUnOp_bounds).
Compute ("Opp overflows? ", sanity_compute roppW ExprUnOp_bounds).
Compute ("Opp overflows (error if it does)? ", sanity_check roppW ExprUnOp_bounds).
