Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.ModOps.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Local Open Scope list_scope.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.

Module DettmanMultiplication.
  Section DettmanMultiplication.
    Context
        (s : Z)
        (c_ : list (Z*Z))
        (limbs : nat)
        (weight: nat -> Z)
        (p_nz : s - Associational.eval c_ <> 0)
        (limbs_gteq_3 : 3%nat <= limbs) (* Technically we only need 2 <= limbs to get the proof to go through, but it doesn't make any sense to try to do this with less than three limbs.
                                           Note that having 3 limbs corresponds to zero iterations of the "loop" function defined below. *)
        (s_small : s <= weight limbs)
        (s_big : weight (limbs - 1)%nat <= s)
        (weight_limbs_mod_s_eq_0 : (weight limbs) mod s = 0)
        (wprops : @weight_properties weight).

    Let c := Associational.eval c_.

    Lemma s_positive : s > 0.
    Proof. remember (weight_positive wprops (limbs - 1)). lia. Qed.

    Lemma s_nz : s <> 0.
    Proof. remember s_positive. lia. Qed.

    Lemma weight_nz : forall i, weight i <> 0.
    Proof. intros i. remember (weight_positive wprops i). lia. Qed.

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

    Hint Resolve s_positive s_nz weight_nz div_nz : arith.
    Hint Resolve weight_0 weight_positive weight_multiples Weight.weight_multiples_full : arith.

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
    Proof. cbv [loop_body carry' reduce']. autorewrite with push_eval; auto with arith. Qed.

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
    Hint Resolve Z_mod_same_full : arith.

    Local Open Scope Z_scope.

    Theorem eval_mulmod a b :
      (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c) =
      (Positional.eval weight limbs (mulmod a b)) mod (s - c).
    Proof.
      cbv [mulmod carry' reduce']. autorewrite with push_eval; auto with arith.
      all: try apply Weight.weight_multiples_full; auto with arith; try lia.
      - apply div_nz; try assumption. remember (weight_positive wprops (limbs - 1)). lia.
      - apply Divide.Z.mod_divide_full in weight_limbs_mod_s_eq_0. destruct weight_limbs_mod_s_eq_0 as [x H].
        rewrite H. rewrite Z_div_mult; try apply s_positive. rewrite Z.mul_comm. rewrite Z_mod_mult. lia.
    Qed.
  End DettmanMultiplication.
End DettmanMultiplication.

Module dettman_multiplication_mod_ops.
  Section dettman_multiplication_mod_ops.
    Import DettmanMultiplication.
    Local Open Scope Z_scope.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    Local Coercion Z.pos : positive >-> Z.
    Context
        (s : Z)
        (c : list (Z*Z))
        (n : nat)
        (last_limb_width : nat)
        (p_nz : s - Associational.eval c <> 0)
        (n_gteq_3 : 3%nat <= n)
        (last_limb_width_small : last_limb_width * n <= Z.log2_up s)
        (last_limb_width_big : 1 <= last_limb_width)
        (s_power_of_2 : 2 ^ (Z.log2 s) = s).

    (* I do want to have Z.log2_up s, not Z.log2_up (s - c) below.  We want to ensure that weight (n - 1) <= s <= weight limbs *)
    Local Notation limbwidth_num := (Z.log2_up s - last_limb_width).
    Local Notation limbwidth_den := (n - 1). (* can't use Q here, or else reification doesn't work *)
    Definition weight := (weight limbwidth_num limbwidth_den).
    
    Definition mulmod := mulmod s c n weight.

    Lemma n_small : n - 1 <= Z.log2_up s - last_limb_width.
    Proof.
      replace (Z.of_nat n) with (Z.of_nat n - 1 + 1) in last_limb_width_small by lia.
      remember (Z.of_nat n - 1) as n'.
      rewrite Z.mul_add_distr_l in last_limb_width_small.
      remember (Z.of_nat last_limb_width) as l.
      assert (H: n' <= l * n').
      { replace n' with (1 * n') by lia. replace (l * (1 * n')) with (l * n') by lia.
        apply Zmult_le_compat_r; lia. }
      lia.
    Qed.

    Lemma limbwidth_good : 0 < limbwidth_den <= limbwidth_num.
    Proof. remember n_small. lia. Qed.

    Local Notation wprops := (@wprops limbwidth_num limbwidth_den limbwidth_good).

    Lemma s_small : s <= weight n.
    Proof.
      rewrite (ModOps.weight_ZQ_correct _ _ limbwidth_good).
      remember (Log2.Z.log2_up_le_full s) as H eqn:clearMe. clear clearMe.
      apply (Z.le_trans _ _ _ H). apply Z.pow_le_mono_r; try lia.
      rewrite Zle_Qle.
      remember (_ *_)%Q as x eqn:E. apply (Qle_trans _ x).
      - subst. rewrite <- (Qmult_le_r _ _ (inject_Z (Z.of_nat n) - 1)).
        + cbv [Qdiv Qminus]. replace 0%Q with (inject_Z 0) by reflexivity.
          replace (-(1))%Q with (inject_Z (-1)) by reflexivity. rewrite <- inject_Z_plus.
          rewrite <- inject_Z_mult. repeat rewrite <- Qmult_assoc. rewrite (Qmult_comm (Qinv _)).
          rewrite <- (Qmult_assoc _ _ (Qinv _)). rewrite Qmult_inv_r.
          -- rewrite Qmult_1_r. rewrite <- inject_Z_mult. rewrite <- Zle_Qle. lia.
          -- replace 0%Q with (inject_Z 0) by reflexivity. rewrite inject_Z_injective. lia.
        + replace 0%Q with (inject_Z 0) by reflexivity.
          replace 1%Q with (inject_Z 1) by reflexivity. cbv [Qminus]. rewrite <- inject_Z_opp.
          rewrite <- inject_Z_plus. rewrite <- Zlt_Qlt. lia.
      - apply Qle_ceiling.
    Qed.

    Lemma s_gt_0 : 0 < s.
      assert (H: s <= 0 \/ 0 < s) by lia. destruct H as [H|H].
      - apply Z.log2_up_nonpos in H. lia.
      - assumption.
    Qed.

    Lemma s_big : weight (n - 1) <= s.
    Proof.
      rewrite (ModOps.weight_ZQ_correct _ _ limbwidth_good).
      remember (Z.log2_spec _ s_gt_0) as H eqn:clearMe. clear clearMe.
      destruct H as [H _].
      apply (Z.le_trans _ (2 ^ Z.log2 s)); try apply H.
      apply Z.pow_le_mono_r; try lia.
      rewrite Zle_Qle. cbv [Qdiv]. rewrite <- (Qmult_assoc _ (Qinv _)).
      rewrite (Qmult_comm (Qinv _)). rewrite Nat2Z.inj_sub; try lia. simpl. cbv [Z.sub].
      rewrite inject_Z_plus. simpl. replace (inject_Z (-1)) with (-(1))%Q by reflexivity.
      cbv [Qminus]. rewrite Qmult_inv_r.
      - rewrite <- inject_Z_plus. rewrite Qmult_1_r. rewrite Qceiling_Z.
        rewrite <- Zle_Qle. remember (Z.le_log2_up_succ_log2 s). lia.
      - replace (-(1))%Q with (inject_Z (-1)) by reflexivity.
        replace 0%Q with (inject_Z 0) by reflexivity. rewrite inject_Z_injective. lia.
    Qed.

    Lemma weight_n_mod_s_eq_0 : weight n mod s = 0.
    Proof.
      cbv [weight ModOps.weight]. remember (- _) as e eqn:E. rewrite <- s_power_of_2.
      apply Modulo.Z.mod_same_pow. split.
      - apply Z.log2_nonneg.
      - assert (H: 0 < 2) by lia. rewrite (Z.pow_le_mono_r_iff 2); try lia.
        + subst. replace (2^(-_)) with (weight n) by reflexivity. rewrite s_power_of_2.
          apply s_small.
        + remember (weight_positive wprops n) as H1 eqn:clearMe. clear clearMe.
          cbv [ModOps.weight] in H1. rewrite <- E in H1.
          assert (H': 0 <= e \/ e < 0) by lia. destruct H' as [H'|H']; try lia.
          apply (Z.pow_neg_r 2 _) in H'. lia.
    Qed.
 
    Definition eval_mulmod := eval_mulmod s c n weight p_nz n_gteq_3 s_small s_big weight_n_mod_s_eq_0 wprops.
  End dettman_multiplication_mod_ops.
End dettman_multiplication_mod_ops.
