Lemma impl_and_iff {A B C} : (A -> (B /\ C)) <-> ((A -> B) /\ (A -> C)).
Proof. tauto. Qed.
