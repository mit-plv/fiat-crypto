Require Crypto.Util.PrimitiveHList.
Require Import Crypto.Rewriter.TestRules.

Lemma test_rewrite_rules_proofs
  : PrimitiveHList.hlist (@snd bool Prop) test_rewrite_rulesT.
Proof using Type. Admitted.
