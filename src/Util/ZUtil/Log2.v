Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Simple.
Local Open Scope Z_scope.

Module Z.
  Lemma log2_nonneg' n a : n <= 0 -> n <= Z.log2 a.
  Proof.
    intros; transitivity 0; auto with zarith.
  Qed.
  Hint Resolve log2_nonneg' : zarith.

  Lemma le_lt_to_log2 x y z : 0 <= z -> 0 < y -> 2^x <= y < 2^z -> x <= Z.log2 y < z.
  Proof.
    destruct (Z_le_gt_dec 0 x); auto with concl_log2 lia.
  Qed.

  Lemma log2_pred_pow2_full a : Z.log2 (Z.pred (2^a)) = Z.max 0 (Z.pred a).
  Proof.
    destruct (Z_dec 0 a) as [ [?|?] | ?].
    { rewrite Z.log2_pred_pow2 by assumption; lia. }
    { autorewrite with zsimplify; simpl.
      apply Z.max_case_strong; try lia.

    }
    { subst; compute; reflexivity. }
  Qed.
  Hint Rewrite log2_pred_pow2_full : zsimplify.

  Lemma log2_up_le_full a : a <= 2^Z.log2_up a.
  Proof.
    destruct (Z_dec 1 a) as [ [ ? | ? ] | ? ];
      first [ apply Z.log2_up_spec; assumption
            | rewrite Z.log2_up_eqn0 by lia; simpl; lia ].
  Qed.

  Lemma log2_up_le_pow2_full : forall a b : Z, (0 <= b)%Z -> (a <= 2 ^ b)%Z <-> (Z.log2_up a <= b)%Z.
  Proof.
    intros a b H.
    destruct (Z_lt_le_dec 0 a); [ apply Z.log2_up_le_pow2; assumption | ].
    split; transitivity 0%Z; try lia; auto with zarith.
    rewrite Z.log2_up_eqn0 by lia.
    reflexivity.
  Qed.

  Lemma log2_lt_pow2_alt a b : 0 < b -> (a < 2^b <-> Z.log2 a < b).
  Proof.
    destruct (Z_lt_le_dec 0 a); auto using Z.log2_lt_pow2; [].
    rewrite Z.log2_nonpos by lia.
    split; auto;[].
    intro; eapply Z.le_lt_trans; [ eassumption | ].
    auto with zarith.
  Qed.

  Lemma max_log2_up x y : Z.max (Z.log2_up x) (Z.log2_up y) = Z.log2_up (Z.max x y).
  Proof. apply Z.max_monotone; intros ??; apply Z.log2_up_le_mono. Qed.
  Hint Rewrite max_log2_up : push_Zmax.
  Hint Rewrite <- max_log2_up : pull_Zmax.

  Lemma log2_up_le_full_max a : Z.max a 1 <= 2^Z.log2_up a.
  Proof.
    apply Z.max_case_strong; auto using Z.log2_up_le_full.
    intros; rewrite Z.log2_up_eqn0 by assumption; reflexivity.
  Qed.
  Lemma log2_up_le_1 a : Z.log2_up a <= 1 <-> a <= 2.
  Proof.
    pose proof (Z.log2_nonneg (Z.pred a)).
    destruct (Z_dec a 2) as [ [ ? | ? ] | ? ].
    { rewrite (proj2 (Z.log2_up_null a)) by lia; split; lia. }
    { rewrite Z.log2_up_eqn by lia.
      split; try lia; intro.
      assert (Z.log2 (Z.pred a) = 0) by lia.
      assert (Z.pred a <= 1) by (apply Z.log2_null; lia).
      lia. }
    { subst; cbv -[Z.le]; split; lia. }
  Qed.
  Lemma log2_up_1_le a : 1 <= Z.log2_up a <-> 2 <= a.
  Proof.
    pose proof (Z.log2_nonneg (Z.pred a)).
    destruct (Z_dec a 2) as [ [ ? | ? ] | ? ].
    { rewrite (proj2 (Z.log2_up_null a)) by lia; split; lia. }
    { rewrite Z.log2_up_eqn by lia; lia. }
    { subst; cbv -[Z.le]; split; lia. }
  Qed.
End Z.
