Require Import Crypto.Specific.GF25519Reflective.Common.

Definition runpackZ_sig : rexpr_unop_WireToFE_sig unpack. Proof. reify_sig. Defined.
Definition runpackW := Eval vm_compute in rword_of_Z runpackZ_sig.
Lemma runpackW_correct_and_bounded_gen : correct_and_bounded_genT runpackW runpackZ_sig.
Proof. rexpr_correct. Qed.
