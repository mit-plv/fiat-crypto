Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rpackZ_sig : rexpr_unop_FEToWire_sig pack. Proof. reify_sig. Defined.
Definition rpackW := Eval vm_compute in rword_of_Z rpackZ_sig.
Lemma rpackW_correct_and_bounded_gen : correct_and_bounded_genT rpackW rpackZ_sig.
Proof. rexpr_correct. Qed.
Definition rpack_output_bounds := Eval vm_compute in compute_bounds rpackW ExprUnOpFEToWire_bounds.

Local Open Scope string_scope.
Compute ("Pack", compute_bounds_for_display rpackW ExprUnOpFEToWire_bounds).
(*Compute ("Pack overflows? ", sanity_check rpackW ExprUnOpFEToWire_bounds).*)
