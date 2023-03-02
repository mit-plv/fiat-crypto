Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Local Open Scope list_scope.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.

Section __.

Context
    (s : Z)
    (c_ : list (Z*Z))
    (p_nz : s - Associational.eval c_ <> 0)
    (limbs : nat)
    (limb_size : nat)
    (weight: nat -> Z)
    (s_small : s <= weight limbs)
    (s_big : weight (limbs - 1)%nat <= s)
    (limbs_gteq_3 : (3 <= limbs)%nat)
    (weight_limbs_mod_s_eq_0 : (weight limbs) mod s = 0)
    (weight_0 : weight 0%nat = 1)
    (weight_positive : forall i, 0 < weight i)
    (weight_multiples : forall i, weight (S i) mod weight i = 0)
    (weight_divides : forall i : nat, 0 < weight (S i) / weight i).

Let c := Associational.eval c_.

Lemma s_positive : s > 0.
Proof. remember (weight_positive (limbs - 1)). lia. Qed.

Lemma s_nz : s <> 0.
Proof. remember s_positive. lia. Qed.

Lemma weight_nz : forall i, weight i <> 0.
Proof. intros i. remember (weight_positive i). lia. Qed.

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
  - apply Weight.weight_multiples_full; try assumption. lia.
  - assumption.
  - apply p_nz.
  - apply weight_nz.
Qed.

Definition loop start :=
  fold_right loop_body start (rev (seq 1 (limbs - 2 - 1))).

Lemma eval_loop start :
  ((Associational.eval (loop start)) mod (s - c) = (Associational.eval start) mod (s - c))%Z.
Proof.
  cbv [loop]. induction (rev (seq 1 (limbs - 2 - 1))) as [| i l' IHl'].
  - reflexivity.
  - simpl. rewrite eval_loop_body. apply IHl'.
Qed.

Definition mulmod a b :=
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
  let r8 := borrow (weight l) (weight l / s) r7 in
  let r8' := dedup_weights r8 in
  let r9 := reduce' s s s c r8' in
  let r10 := carry' (weight 0) (weight 1) r9 in
  let r11 := loop r10 in
  let r12 := reduce' s (weight (2 * l - 2)) (weight l) c r11 in
  let r13 := carry' (weight (l - 2)) (weight 1) r12 in
  Positional.from_associational weight l r13.

Hint Rewrite Positional.eval_from_associational Positional.eval_to_associational eval_borrow eval_loop: push_eval.

Local Open Scope Z_scope.

Theorem eval_mulmod a b :
  (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c) =
  (Positional.eval weight limbs (mulmod a b)) mod (s - c).
Proof.
  cbv [mulmod carry' reduce']. autorewrite with push_eval. reflexivity.
  all:
    try apply weight_nz;
    try apply s_nz;
    try apply p_nz;
    try apply weight_0;
    try apply Z_mod_same_full;
    try apply weight_limbs_mod_s_eq_0;
    try apply Weight.weight_multiples_full;
    try assumption;
    try lia.
  - apply div_nz; try assumption. remember (weight_positive (limbs - 1)). lia.
  - apply div_nz; try lia. apply s_positive.
  - apply Divide.Z.mod_divide_full in weight_limbs_mod_s_eq_0. destruct weight_limbs_mod_s_eq_0 as [x H].
    rewrite H. rewrite Z_div_mult; try apply s_positive. rewrite Z.mul_comm. rewrite Z_mod_mult. lia.
Qed.

End __.
