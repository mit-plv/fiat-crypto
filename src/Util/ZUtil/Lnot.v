Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Module Z.
  Lemma lnot_equiv n : Z.lnot n = Z.pred (-n).
  Proof. reflexivity. Qed.

  Lemma lnot_sub1 n : Z.lnot (n-1) = -n.
  Proof. rewrite lnot_equiv; lia. Qed.

  Lemma lnot_opp x : Z.lnot (- x) = x-1.
  Proof.
    rewrite <-Z.lnot_involutive, lnot_sub1; reflexivity.
  Qed.
End Z.
