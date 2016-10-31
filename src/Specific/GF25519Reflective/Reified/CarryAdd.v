Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_addZ_sig : rexpr_binop_sig carry_add. Proof. reify_sig. Defined.
Definition rcarry_addW := Eval vm_compute in rword_of_Z rcarry_addZ_sig.
Lemma rcarry_addW_correct_and_bounded_gen : correct_and_bounded_genT rcarry_addW rcarry_addZ_sig.
Proof. rexpr_correct. Qed.
