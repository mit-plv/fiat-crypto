Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Local Open Scope list_scope.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion Z.pos : positive >-> Z.

Section __.

Context
        (e : nat)
        (c_ : list (Z*Z))
        (p_nz : 2 ^ e - Associational.eval c_ <> 0)
        (limbs : nat)
        (limb_size : nat)
        (limbs_gteq_3 : (3 <= limbs)%nat)
        (e_small : (e <= limb_size * limbs)%nat)
        (e_big : (limb_size * (limbs - 1) <= e)%nat).

Let s := (2 ^ e).

Let c := Associational.eval c_.

Let base := (2 ^ limb_size).

Lemma base_nz : base <> 0.
Proof. cbv [base]. apply Z.pow_nonzero; lia. Qed.

Lemma s_nz : s <> 0.
Proof. cbv [s]. apply Z.pow_nonzero; lia. Qed.

Let weight (n : nat) := base ^ n.

Lemma weight_0 : weight 0 = 1.
Proof. reflexivity. Qed.

Lemma weight_nz : forall i, weight i <> 0.
Proof. intros i. cbv [weight]. apply Z.pow_nonzero; lia. Qed.

Lemma mod_is_zero : forall b (n m : nat), b <> 0 -> le n m -> (b ^ m) mod (b ^ n) = 0.
  intros b n m H1 H2. induction H2 as [|m' nlem' IHm'].
  - rewrite Z_mod_same_full. constructor.
  - rewrite Nat2Z.inj_succ. cbv [Z.succ]. rewrite <- Pow.Z.pow_mul_base by lia.
    rewrite Z.mul_mod_full. rewrite IHm'. rewrite Z.mul_0_r. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.

Lemma div_nz a b : b > 0 -> b <= a -> a / b <> 0.
Proof.
  intros H1 H2. assert (H: 1 <= a / b).
  - replace 1 with (b / b).
    + apply Z_div_le; assumption.
    + apply Z_div_same. apply H1.
  - symmetry. apply Z.lt_neq. apply Z.lt_le_trans with 1.
    + reflexivity.
    + apply H.
Qed.

Lemma limbs_mod_s_0 : (weight limbs) mod s = 0.
Proof.
  cbv [weight base s]. rewrite <- Z.pow_mul_r by lia. rewrite <- Nat2Z.inj_mul. apply mod_is_zero; lia.
Qed.

Local Open Scope nat_scope.

Definition reduce' x1 x2 x3 x4 x5 := dedup_weights (reduce_one x1 x2 x3 x4 x5).
Definition carry' x1 x2 x3 := dedup_weights (Associational.carry x1 x2 x3).

Definition loop_body i before :=
  let middle1 := carry' (weight (i + limbs)) (weight 1) before in
  let middle2 := reduce' s (weight (i + limbs)) (weight limbs) c middle1 in
  let after := carry' (weight i) (weight 1) middle2 in
  after.

Hint Rewrite eval_reduce_one Associational.eval_carry eval_dedup_weights: push_eval.

Lemma eval_loop_body i before :
  (Associational.eval (loop_body i before) mod (s - c) =
  Associational.eval before mod (s - c))%Z.
Proof.
  cbv [loop_body carry' reduce']. autorewrite with push_eval. reflexivity.
  - apply weight_nz.
  - apply s_nz.
  - apply weight_nz.
  - cbv [weight]. apply mod_is_zero.
    + apply base_nz.
    + lia.
  - cbv [weight]. apply limbs_mod_s_0.
  - apply p_nz.
  - apply weight_nz.
Qed.

Definition from_n_to_one n :=
  fold_right (fun (x :nat) l' => (length l' + 1) :: l') [] (repeat 0 n).

Definition loop' start :=
  fold_right loop_body start (from_n_to_one (limbs - 2 - 1)).

Lemma eval_loop' start :
  ((Associational.eval (loop' start)) mod (s - c) = (Associational.eval start) mod (s - c))%Z.
Proof.
  cbv [loop']. induction (from_n_to_one (limbs - 2 - 1)) as [| i l' IHl'].
  - reflexivity.
  - simpl. rewrite eval_loop_body. apply IHl'.
Qed.

Definition mulmod_general a b :=
  let l := limbs in
  let a_assoc := Positional.to_associational weight limbs a in
  let b_assoc := Positional.to_associational weight limbs b in
  let r0 := Associational.mul a_assoc b_assoc in
  let r0' := dedup_weights r0 in
  let r1 := carry' (weight (2 * l - 2)) (weight 1) r0' in
  let r2 := reduce' s (weight (2 * l - 2)) (weight l) c r1 in
  let r3 := carry' (weight (l - 2)) (weight 1) r2 in
  let r4 := reduce' s (weight (2 * l - 1)) (weight l) c r3 in
  let r5 := carry' (weight (l - 1)) (weight 1) r4 in
  let r6 := carry' (weight (l - 1)) (Z.div s (weight (l - 1))) r5 in
  let r7 := carry' (weight l) (weight 1) r6 in
  let r8 := carry_down (weight l) (weight l / s) r7 in
  let r8' := dedup_weights r8 in
  let r9 := reduce' s s s c r8' in
  let r10 := carry' (weight 0) (weight 1) r9 in
  let r11 := loop' r10 in
  let r12 := reduce' s (weight (2 * l - 2)) (weight l) c r11 in
  let r13 := carry' (weight (l - 2)) (weight 1) r12 in
  Positional.from_associational weight l r13.

Hint Rewrite Positional.eval_from_associational Positional.eval_to_associational eval_carry_down eval_loop': push_eval.

Local Open Scope Z_scope.

Theorem eval_mulmod_general a b :
  (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c) =
  (Positional.eval weight limbs (mulmod_general a b)) mod (s - c).
Proof.
  cbv [mulmod_general carry' reduce']. autorewrite with push_eval. reflexivity.
  all:
      cbv [weight s base];
      try apply weight_nz;
      try apply s_nz;
      try apply p_nz;
      try apply weight_0;
      try apply Z_mod_same_full;
      try apply limbs_mod_s_0;
      try apply mod_is_zero;
      try (remember limbs_gteq_3 as H; lia);
      try apply base_nz.
  - apply div_nz; try lia. rewrite <- Z.pow_mul_r by lia. rewrite <- Nat2Z.inj_mul.
    rewrite <- Z.pow_le_mono_r_iff by lia. lia.
  - apply div_nz; try lia. rewrite <- Z.pow_mul_r by lia. rewrite <- Nat2Z.inj_mul.
    rewrite <- Z.pow_le_mono_r_iff by lia. lia.
  - repeat rewrite <- Z.pow_mul_r by lia. rewrite <- Z.pow_sub_r by lia.
    rewrite <- Nat2Z.inj_mul. rewrite <- Nat2Z.inj_sub by lia. apply mod_is_zero; lia.
Qed.

End __.
