Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rpackZ_sig : rexpr_unop_FEToWire_sig pack. Proof. reify_sig. Defined.
Definition rpackW := Eval vm_compute in rword_of_Z rpackZ_sig.
Lemma rpackW_correct_and_bounded_gen : correct_and_bounded_genT rpackW rpackZ_sig.
Proof. rexpr_correct. Qed.
