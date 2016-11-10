Require Import Crypto.Specific.GF25519Reflective.CommonUnOpFEToZ.

Definition rge_modulusZ_sig : rexpr_unop_FEToZ_sig ge_modulus. Proof. reify_sig. Defined.
Definition rge_modulusW := Eval vm_compute in rword_of_Z rge_modulusZ_sig.
Lemma rge_modulusW_correct_and_bounded_gen : correct_and_bounded_genT rge_modulusW rge_modulusZ_sig.
Proof. rexpr_correct. Qed.
Definition rge_modulus_output_bounds := Eval vm_compute in compute_bounds rge_modulusW ExprUnOpFEToZ_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rge_modulusW_correct_and_bounded
  := ExprUnOpFEToZ_correct_and_bounded
       rge_modulusW ge_modulus rge_modulusZ_sig rge_modulusW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Ge_Modulus", compute_bounds_for_display rge_modulusW ExprUnOpFEToZ_bounds).
Compute ("Ge_Modulus overflows? ", sanity_compute rge_modulusW ExprUnOpFEToZ_bounds).
Compute ("Ge_Modulus overflows (error if it does)? ", sanity_check rge_modulusW ExprUnOpFEToZ_bounds).
