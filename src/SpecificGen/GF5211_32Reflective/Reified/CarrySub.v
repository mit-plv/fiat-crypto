Require Import Crypto.SpecificGen.GF5211_32Reflective.CommonBinOp.

Definition rcarry_subZ_sig : rexpr_binop_sig carry_sub. Proof. reify_sig. Defined.
Definition rcarry_subW := Eval vm_compute in rword_of_Z rcarry_subZ_sig.
Lemma rcarry_subW_correct_and_bounded_gen : correct_and_bounded_genT rcarry_subW rcarry_subZ_sig.
Proof. rexpr_correct. Qed.
Definition rcarry_sub_output_bounds := Eval vm_compute in compute_bounds rcarry_subW ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_subW_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rcarry_subW carry_sub rcarry_subZ_sig rcarry_subW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Carry_Sub", compute_bounds_for_display rcarry_subW ExprBinOp_bounds).
Compute ("Carry_Sub overflows? ", sanity_compute rcarry_subW ExprBinOp_bounds).
Compute ("Carry_Sub overflows (error if it does)? ", sanity_check rcarry_subW ExprBinOp_bounds).
