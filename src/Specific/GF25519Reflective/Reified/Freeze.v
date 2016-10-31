Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rfreezeZ_sig : rexpr_unop_sig freeze. Proof. reify_sig. Defined.
Definition rfreezeW := Eval vm_compute in rword_of_Z rfreezeZ_sig.
Lemma rfreezeW_correct_and_bounded_gen : correct_and_bounded_genT rfreezeW rfreezeZ_sig.
Proof. rexpr_correct. Qed.
