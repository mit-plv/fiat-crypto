Require Import Crypto.Specific.GF25519Reflective.Common.

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.
Definition raddW := Eval vm_compute in rword_of_Z raddZ_sig.
Lemma raddW_correct_and_bounded_gen : correct_and_bounded_genT raddW raddZ_sig.
Proof. rexpr_correct. Qed.
