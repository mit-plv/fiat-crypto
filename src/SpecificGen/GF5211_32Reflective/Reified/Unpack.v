Require Import Crypto.SpecificGen.GF5211_32Reflective.CommonUnOpWireToFE.

Definition runpackZ_sig : rexpr_unop_WireToFE_sig unpack. Proof. reify_sig. Defined.
Definition runpackW := Eval vm_compute in rword_of_Z runpackZ_sig.
Lemma runpackW_correct_and_bounded_gen : correct_and_bounded_genT runpackW runpackZ_sig.
Proof. rexpr_correct. Qed.
Definition runpack_output_bounds := Eval vm_compute in compute_bounds runpackW ExprUnOpWireToFE_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition runpackW_correct_and_bounded
  := ExprUnOpWireToFE_correct_and_bounded
       runpackW unpack runpackZ_sig runpackW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Unpack", compute_bounds_for_display runpackW ExprUnOpWireToFE_bounds).
Compute ("Unpack overflows? ", sanity_compute runpackW ExprUnOpWireToFE_bounds).
Compute ("Unpack overflows (error if it does)? ", sanity_check runpackW ExprUnOpWireToFE_bounds).
