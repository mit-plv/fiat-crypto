Require Import Crypto.SpecificGen.GF41417_32Reflective.CommonBinOp.

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Defined.
Definition rmulW := Eval vm_compute in rword_of_Z rmulZ_sig.
Lemma rmulW_correct_and_bounded_gen : correct_and_bounded_genT rmulW rmulZ_sig.
Proof. rexpr_correct. Qed.
Definition rmul_output_bounds := Eval vm_compute in compute_bounds rmulW ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rmulW_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rmulW mul rmulZ_sig rmulW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Mul", compute_bounds_for_display rmulW ExprBinOp_bounds).
Compute ("Mul overflows? ", sanity_compute rmulW ExprBinOp_bounds).
Compute ("Mul overflows (error if it does)? ", sanity_check rmulW ExprBinOp_bounds).
