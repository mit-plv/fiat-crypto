Require Import Coq.ZArith.ZArith.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.

Lemma neg_nonneg : forall x y, 0 <= x -> 0 <= ModularBaseSystemListZOperations.neg x y.
Proof.
  unfold neg; intros; break_match; auto with zarith.
Qed.
Hint Resolve neg_nonneg : zarith.

Lemma neg_upperbound : forall x y, 0 <= x -> ModularBaseSystemListZOperations.neg x y <= Z.ones x.
Proof.
  unfold neg; intros; break_match; auto with zarith.
Qed.
Hint Resolve neg_upperbound : zarith.

Lemma neg_range : forall x y, 0 <= x ->
  0 <= neg x y < 2 ^ x.
Proof.
  intros.
  split; auto using neg_nonneg.
  eapply Z.le_lt_trans; eauto using neg_upperbound.
  rewrite Z.ones_equiv.
  omega.
Qed.
