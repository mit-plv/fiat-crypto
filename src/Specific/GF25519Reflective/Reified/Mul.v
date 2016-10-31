Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Defined.
Definition rmulW := Eval vm_compute in rword_of_Z rmulZ_sig.
Lemma rmulW_correct_and_bounded_gen : correct_and_bounded_genT rmulW rmulZ_sig.
Proof. rexpr_correct. Qed.
