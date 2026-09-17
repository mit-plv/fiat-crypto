From Coq Require Import ZArith.
From Coq Require Import Lia.
Local Open Scope Z_scope.

Module Z.
  Lemma mul_comm3 x y z : x * (y * z) = y * (x * z).
  Proof. lia. Qed.

  Lemma mul_eq_1_iff a b : a*b = 1 <-> a = 1 /\ b = 1 \/ a = -1 /\ b = -1.
  Proof. pose proof Z.eq_mul_1 a b; nia. Qed.
End Z.
