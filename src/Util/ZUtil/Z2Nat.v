Require Import Coq.ZArith.ZArith Coq.micromega.Lia.

Local Open Scope Z_scope.
Module Z2Nat.
  Definition inj_nonpos n : n <= 0 -> Z.to_nat n = 0%nat.
  Proof.
    destruct n; try reflexivity; lia.
  Qed.
End Z2Nat.

Module Z.
  Lemma pos_pow_nat_pos : forall x n,
    Z.pos x ^ Z.of_nat n > 0.
  Proof. intros; apply Z.lt_gt, Z.pow_pos_nonneg; lia. Qed.

  Lemma pow_Z2N_Zpow : forall a n, 0 <= a ->
                                   ((Z.to_nat a) ^ n = Z.to_nat (a ^ Z.of_nat n)%Z)%nat.
  Proof.
    intros a n H; induction n as [|n IHn]; try reflexivity.
    rewrite Nat2Z.inj_succ.
    rewrite Nat.pow_succ_r by apply le_0_n.
    rewrite Z.pow_succ_r by apply Zle_0_nat.
    rewrite IHn.
    rewrite Z2Nat.inj_mul; auto using Z.pow_nonneg.
  Qed.

  Lemma pow_Zpow : forall a n : nat, Z.of_nat (a ^ n) = Z.of_nat a ^ Z.of_nat n.
  Proof with auto using Zle_0_nat, Z.pow_nonneg.
    intros; apply Z2Nat.inj...
    rewrite <- pow_Z2N_Zpow, !Nat2Z.id...
  Qed.
  Hint Rewrite pow_Zpow : push_Zof_nat.
  Hint Rewrite <- pow_Zpow : pull_Zof_nat.

  Lemma Zpow_sub_1_nat_pow a v
    : (Z.pos a^Z.of_nat v - 1 = Z.of_nat (Z.to_nat (Z.pos a)^v - 1))%Z.
  Proof.
    rewrite <- (Z2Nat.id (Z.pos a)) at 1 by lia.
    change 2%Z with (Z.of_nat 2); change 1%Z with (Z.of_nat 1);
      autorewrite with pull_Zof_nat.
    rewrite Nat2Z.inj_sub
      by (change 1%nat with (Z.to_nat (Z.pos a)^0)%nat; apply Nat.pow_le_mono_r; simpl; lia).
    reflexivity.
  Qed.
  Hint Rewrite Zpow_sub_1_nat_pow : pull_Zof_nat.
  Hint Rewrite <- Zpow_sub_1_nat_pow : push_Zof_nat.
End Z.
