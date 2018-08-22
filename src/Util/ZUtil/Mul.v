Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Module Z.
  Lemma mul_comm3 x y z : x * (y * z) = y * (x * z).
  Proof. lia. Qed.
End Z.
