Require Export Crypto.Util.FixCoqMistakes.

Lemma pull_exists_iff {A} {P Q : A -> Prop}
  : (forall x : A, P x <-> Q x) -> ((exists x, P x) <-> (exists x, Q x)).
Proof. firstorder. Qed.
