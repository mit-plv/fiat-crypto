Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_oppZ_sig : rexpr_unop_sig carry_opp. Proof. reify_sig. Defined.
Definition rcarry_oppW := Eval vm_compute in rword_of_Z rcarry_oppZ_sig.
Lemma rcarry_oppW_correct_and_bounded_gen : correct_and_bounded_genT rcarry_oppW rcarry_oppZ_sig.
Proof. rexpr_correct. Qed.
