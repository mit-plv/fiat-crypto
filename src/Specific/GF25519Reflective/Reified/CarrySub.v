Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_subZ_sig : rexpr_binop_sig carry_sub. Proof. reify_sig. Defined.
Definition rcarry_subW := Eval vm_compute in rword_of_Z rcarry_subZ_sig.
Lemma rcarry_subW_correct_and_bounded_gen : correct_and_bounded_genT rcarry_subW rcarry_subZ_sig.
Proof. rexpr_correct. Qed.
