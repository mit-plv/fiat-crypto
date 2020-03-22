Require Export Crypto.Util.FixCoqMistakes.

Lemma pull_forall_and {A} {P Q : A -> Prop}
  : (forall x : A, P x /\ Q x) <-> ((forall x, P x) /\ (forall x, Q x)).
Proof. firstorder. Qed.

Lemma pull_forall_iff {A} {P Q : A -> Prop}
  : (forall x : A, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).
Proof. firstorder. Qed.
