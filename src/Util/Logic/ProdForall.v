Require Export Crypto.Util.FixCoqMistakes.

Lemma pull_prod_forall A A' B B' (Q : A * A' -> B * B' -> Prop)
: (forall x y, Q x y) <-> (forall x0 y0 x1 y1, Q (x0, x1) (y0, y1)).
Proof. intuition. Qed.
