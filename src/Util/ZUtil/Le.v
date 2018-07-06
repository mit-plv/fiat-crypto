Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Module Z.
  Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
  Proof. intros; omega. Qed.
  Hint Resolve positive_is_nonzero : zarith.
End Z.
