Require Import Coq.ZArith.ZArith Coq.micromega.Lia.

Local Open Scope Z_scope.
Module Z2Nat.
  Definition inj_nonpos n : n <= 0 -> Z.to_nat n = 0%nat.
  Proof.
    destruct n; try reflexivity; lia.
  Qed.
End Z2Nat.
