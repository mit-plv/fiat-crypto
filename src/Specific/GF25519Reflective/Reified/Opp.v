Require Import Crypto.Specific.GF25519Reflective.Common.

Definition roppZ_sig : rexpr_unop_sig opp. Proof. reify_sig. Defined.
Definition roppW := Eval vm_compute in rword_of_Z roppZ_sig.
Lemma roppW_correct_and_bounded_gen : correct_and_bounded_genT roppW roppZ_sig.
Proof. rexpr_correct. Qed.
