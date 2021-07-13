Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Hints.PullPush.

Module Nat2Z.
  Lemma inj_pow (n m : nat) : Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
  Proof.
    induction m as [|m IH].
    { rewrite Nat.pow_0_r, Z.pow_0_r; reflexivity. }
    { autorewrite with push_Zof_nat.
      rewrite Nat.pow_succ_r', Z.pow_succ_r, <- IH by lia.
      autorewrite with push_Zof_nat.
      reflexivity. }
  Qed.
  Hint Rewrite inj_pow : push_Zof_nat.
  Hint Rewrite <- inj_pow : pull_Zof_nat.
End Nat2Z.
Hint Rewrite Nat2Z.inj_pow : push_Zof_nat.
Hint Rewrite <- Nat2Z.inj_pow : pull_Zof_nat.
