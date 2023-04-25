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
        (register_width : nat)
        (limbs : nat)
        (weight: nat -> Z)
        (p_nz : s - Associational.eval c_ <> 0)
        (limbs_gteq_4 : 3%nat <= limbs) (* Technically we only need 2 <= limbs to get the proof to go through, but it doesn't make any sense to try to do this with less than three limbs.
                                           Note that having 4 limbs corresponds to zero iterations of the "loop" function defined below. *)
        (s_big : weight (limbs - 1)%nat <= s)
        (weight_lt_width : forall i: nat, (weight i * 2^register_width) mod weight (i + 1)%nat = 0)
        (s_small : forall i: nat, (weight (i + limbs)%nat / weight i) mod s = 0)
        (wprops : @weight_properties weight).

    Context
        (weight_0 := weight_0 wprops)
        (weight_positive := weight_positive wprops)
        (weight_multiples := weight_multiples wprops)
        (weight_divides := weight_divides wprops).
    
    Let c := Associational.eval c_.

    Lemma s_positive : s > 0.
    Proof. remember (weight_positive (limbs - 1)). lia. Qed.

    Lemma s_nz : s <> 0.
    Proof. remember s_positive. lia. Qed.

    Lemma weight_nz : forall i, weight i <> 0.
    Proof. intros i. remember (weight_positive i). lia. Qed.

    Lemma div_mul_le : forall x y, y > 0 -> x / y * y <= x.
    Proof. intros x y H. remember (Zmod_eq x y H). remember (Z_mod_lt x y H). lia. Qed.

    Lemma weight_increasing : forall i j : nat, (i <= j)%nat -> weight i <= weight j.
    Proof.
      intros i j H.
      assert (0 < weight j / weight i). { apply Weight.weight_divides_full; try assumption. }
      assert (1 <= weight j / weight i) by lia.
      assert (1 * weight i <= weight j / weight i * weight i).
      { apply Zmult_le_compat_r; try lia. remember (weight_positive i). lia. }
      apply (Z.le_trans _ (weight j / weight i * weight i) _).
      - lia.
      - (*rewrite Weight.weight_div_mod.*) apply div_mul_le. remember (weight_positive i). lia.
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

    Lemma weight_div_nz : forall i j : nat, (i <= j)%nat -> weight j / weight i <> 0.
    Proof.
      intros i j H.
      assert (0 < weight j / weight i). { apply Weight.weight_divides_full; assumption. }
      lia.
    Qed.

    Lemma mod_quotient_zero : forall x y, 0 < y -> x mod y = 0 -> x mod (x / y) = 0.
    Proof.
      intros x y H H1. rewrite Divide.Z.mod_divide_full in H1. destruct H1 as [z H1].
      subst. rewrite Z_div_mult by lia. rewrite Z.mul_comm. apply Z_mod_mult.
    Qed.
    
    Lemma weight_mod_quotient_zero : forall i j : nat, (i <= j)%nat ->
                                                       (weight j) mod (weight j / weight i) = 0.
    Proof.
      intros i j H. apply mod_quotient_zero; try apply weight_positive.
      apply Weight.weight_multiples_full; assumption.
    Qed.

    Lemma divisible_implies_nonzero a b : 
      a mod b = 0 ->
      a <> 0 ->
      a / b <> 0.
    Proof. intros H1 H2. remember (Z_div_mod_eq_full a b). lia. Qed.
      
    Hint Resolve s_positive s_nz weight_nz div_nz : arith.
    Hint Resolve weight_0 weight_positive weight_multiples Weight.weight_multiples_full : arith.
    Hint Resolve weight_div_nz weight_mod_quotient_zero : arith.
    
    Local Open Scope nat_scope.

    Definition reduce' x1 x2 x3 x4 x5 := dedup_weights (reduce_one x1 x2 x3 x4 x5).
    Definition carry' x1 x2 x3 := dedup_weights (Associational.carry x1 x2 x3).

    Definition loop_body i before :=
      
      let from1 := weight (i + limbs) in
      let to1 := weight (i + limbs + 1) in
      let middle1 := carry' from1 (to1 / from1) before in

      let from2 := weight (i + limbs) in
      let to2 := weight i in
      let middle2 := reduce' s from2 (from2 / to2) c middle1 in

      let from := weight i in
      let to := weight (i + 1) in
      let after := carry' from (to / from) middle2 in
      after.

    Hint Rewrite eval_reduce_one Associational.eval_carry eval_dedup_weights: push_eval.

    Lemma eval_loop_body i before :
      (Associational.eval (loop_body i before) mod (s - c) =
         Associational.eval before mod (s - c))%Z.
    Proof. cbv [loop_body carry' reduce']. autorewrite with push_eval; auto with arith. Qed.

    Definition loop start :=
      fold_right loop_body start (rev (seq 1 (limbs - 2 - 1 - 1))).

    Lemma eval_loop start :
      ((Associational.eval (loop start)) mod (s - c) = (Associational.eval start) mod (s - c))%Z.
    Proof.
      cbv [loop]. induction (rev (seq 1 (limbs - 2 - 1 - 1))) as [| i l' IHl'].
      - reflexivity.
      - simpl. rewrite eval_loop_body. apply IHl'.
    Qed.

    Definition reduce_carry_borrow r0 :=
      let l := limbs in
      let r0' := dedup_weights r0 in
      
      let r1 := carry' (weight (2 * l - 2)) (2^register_width) r0' in
      
      let from2 := weight (2 * l - 2) in
      let to2 := weight (l - 2) in
      let r2 := reduce' s from2 (from2 / to2) c r1 in

      let from3 := weight (l - 2) in
      let to3 := weight (l - 1) in
      let r3 := carry' from3 (to3 / from3) r2 in
      
      let from4 := Z.mul (weight (2 * l - 2)) (2^register_width) in
      let to4 := weight (l - 1) in
      let r4 := reduce' s from4 (from4 / to4) c r3 in

      let from5 := weight (l - 1) in
      let to5 := weight l in
      let r5 := carry' from5 (to5 / from5) r4 in

      let from6 := weight (l - 1) in
      let to6 := s in
      let r6 := carry' from6 (to6 / from6) r5 in

      let from7 := weight l in
      let to7 := weight (l + 1) in
      let r7 := carry' from7 (to7 / from7) r6 in

      let from8 := weight l in
      let to8 := s in
      let r8 := borrow from8 (from8 / to8) r7 in
      
      let r8' := dedup_weights r8 in
      
      let r9 := reduce' s s s c r8' in

      let from10 := weight 0 in
      let to10 := weight 1 in
      let r10 := carry' from10 (to10 / from10) r9 in
      
      let r11 := loop r10 in
      
      (* here I've pulled out the final iteration of the loop to do
         the special register_width carry. *)
      (* begin loop iteration *)
      let i0 := l - 2 - 1 in
      
      let rloop1 := carry' (weight (i0 + limbs)) (2^register_width) r11 in

      let fromLoop2 := weight (i0 + limbs) in
      let toLoop2 := weight i0 in
      let rloop2 := reduce' s fromLoop2 (fromLoop2 / toLoop2) c rloop1 in

      let fromLoop3 := weight i0 in
      let toLoop3 := weight (i0 + 1) in
      let rloop3 := carry' fromLoop3 (toLoop3 / fromLoop3) rloop2 in
      (* end loop iteration*)
      
      let from12 := Z.mul (weight (i0 + limbs)) (2^register_width) in
      let to12 := weight (i0 + 1) in
      let r12 := reduce' s from12 (from12 / to12) c rloop3 in

      let from13 := weight (l - 2) in
      let to13 := weight (l - 1) in
      let r13 := carry' from13 (to13 / from13) r12 in
      
      Positional.from_associational weight l r13.

    Definition mulmod a b :=
      let a_assoc := Positional.to_associational weight limbs a in
      let b_assoc := Positional.to_associational weight limbs b in
      let r0 := Associational.mul a_assoc b_assoc in
      reduce_carry_borrow r0.

    Definition squaremod a :=
      let a_assoc := Positional.to_associational weight limbs a in
      let r0 := Associational.square a_assoc in
      reduce_carry_borrow r0.

    Hint Rewrite Positional.eval_from_associational Positional.eval_to_associational eval_borrow eval_loop: push_eval.
    Hint Resolve Z_mod_same_full : arith.

    Local Open Scope Z_scope.

    Lemma eval_reduce_carry_borrow r0 :
      (Positional.eval weight limbs (reduce_carry_borrow r0)) mod (s - c) =
      (Associational.eval r0) mod (s - c).
    Proof. 
      cbv [reduce_carry_borrow carry' reduce']. autorewrite with push_eval; auto with arith.
      all: try apply weight_div_nz; try lia.
      all: try apply weight_mod_quotient_zero; try lia.
      (*(weight (2 * limbs - 2) / weight (limbs - 2)) mod s = 0*)
      1: { replace (2 * limbs - 2)%nat with ((limbs - 2) + limbs)%nat by lia. apply s_small. }
      (*  s / weight (limbs - 1) <> 0 *)
      4: { apply div_nz; auto with arith. remember (weight_positive (limbs - 1)). lia. }
      (* weight limbs mod (weight limbs / s) = 0 *)
      5: { apply mod_quotient_zero.
           + remember s_positive. lia.
           + replace (weight limbs) with (weight (0 + limbs) / weight 0).
             -- apply s_small.
             -- rewrite weight_0. rewrite Z.div_1_r. rewrite Nat.add_0_l. reflexivity. }
      (*(weight (limbs - 2 - 1 + limbs) * 2 ^ Z.of_nat register_width / weight (limbs - 2 - 1 + 1)) mod s = 0*)
      7: { rewrite Divide.Z.mod_divide_full.
           remember (s_small (limbs - 2 - 1 + 1)) as H eqn:clearMe. clear clearMe.
           apply (Z.divide_trans _ (weight (2*limbs - 2) / weight (limbs - 2))).
           - rewrite <- Divide.Z.mod_divide_full.
             replace (2*limbs-2)%nat with (limbs - 2 + limbs)%nat by lia. apply s_small.
           - replace (limbs - 2 - 1 + 1)%nat with (limbs - 2)%nat by lia. apply Z.divide_div.
             + remember (weight_positive (limbs-2)). lia.
             + rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption.
               lia.
             + rewrite <- Divide.Z.mod_divide_full. replace (2 * limbs - 2)%nat with (limbs - 2 - 1 + limbs + 1)%nat by lia. apply weight_lt_width. }
      (* (weight (limbs - 2 - 1 + limbs) * 2 ^ Z.of_nat register_width)
 mod (weight (limbs - 2 - 1 + limbs) * 2 ^ Z.of_nat register_width / weight (limbs - 2 - 1 + 1)) =
 0 *)
      6: { apply mod_quotient_zero; try apply weight_positive. apply Divide.Z.mod_divide_full. apply Z.divide_mul_l. rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption. lia. }
      (* (weight (2 * limbs - 2) * 2 ^ Z.of_nat register_width)
 mod (weight (2 * limbs - 2) * 2 ^ Z.of_nat register_width / weight (limbs - 1)) = 0 *)
      2: { apply mod_quotient_zero; try apply weight_positive. apply Divide.Z.mod_divide_full. apply Z.divide_mul_l. rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption. lia. }
      (* weight (2 * limbs - 2) * 2 ^ Z.of_nat register_width / weight (limbs - 1) <> 0 *)
      1: { apply divisible_implies_nonzero.
           - rewrite Divide.Z.mod_divide_full. apply Z.divide_mul_l. rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption. lia.
           - Search (_ * _ <> 0). rewrite <- Z.neq_mul_0. split.
             + remember (weight_positive (2 * limbs - 2)). lia.
             + assert (0 < 2^register_width). { Search (0 < 2^_). apply Pow2.Z.pow2_gt_0. lia. }
               lia.
      }
      (* weight limbs / s <> 0 *)
      2: { apply divisible_implies_nonzero.
           - replace (weight limbs) with (weight (0 + limbs) / weight 0).
             + apply s_small.
             + rewrite weight_0. rewrite Z.div_1_r. rewrite Nat.add_0_l. reflexivity.
           - remember (weight_positive limbs). lia.
      }
      (* weight (limbs - 2 - 1 + limbs) * 2 ^ Z.of_nat register_width / weight (limbs - 2 - 1 + 1) <> 0 *)
      2: { apply divisible_implies_nonzero.
           - rewrite Divide.Z.mod_divide_full. apply Z.divide_mul_l. rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption. lia.
           - Search (_ * _ <> 0). rewrite <- Z.neq_mul_0. split.
             + remember (weight_positive (limbs - 2 - 1 + limbs)). lia.
             + assert (0 < 2^register_width). { Search (0 < 2^_). apply Pow2.Z.pow2_gt_0. lia. }
               lia.
      }
      
      (* (weight (2 * limbs - 2) * 2 ^ Z.of_nat register_width / weight (limbs - 1)) mod s = 0 *)
      1: { rewrite Divide.Z.mod_divide_full.
           remember (s_small (limbs - 1)) as H eqn:clearMe. clear clearMe.
           apply (Z.divide_trans _ (weight (2 * limbs - 1) / weight (limbs - 1))).
           - rewrite <- Divide.Z.mod_divide_full.
             replace (2*limbs-1)%nat with (limbs - 1 + limbs)%nat by lia. apply s_small.
           - Search ((_ / _) | (_ / _)). apply Z.divide_div.
             + remember (weight_positive (limbs-1)). lia.
             + rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption.
               lia.
             + rewrite <- Divide.Z.mod_divide_full. replace (2 * limbs - 1)%nat with (2 * limbs - 2 + 1)%nat by lia. apply weight_lt_width.
      }
    Qed.

    Hint Rewrite eval_reduce_carry_borrow : push_eval.

    Theorem eval_mulmod a b :
      (Positional.eval weight limbs (mulmod a b)) mod (s - c) =
      (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c).
    Proof.
      cbv [mulmod]. autorewrite with push_eval. reflexivity.
    Qed.

    Theorem eval_squaremod a :
      (Positional.eval weight limbs (squaremod a)) mod (s - c) =
      (Positional.eval weight limbs a * Positional.eval weight limbs a) mod (s - c).
    Proof.
      cbv [squaremod]. autorewrite with push_eval. reflexivity.
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
    Definition squaremod := squaremod s c n weight.

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
    Definition eval_squaremod := eval_squaremod s c n weight p_nz n_gteq_3 s_small s_big weight_n_mod_s_eq_0 wprops.
  End dettman_multiplication_mod_ops.
End dettman_multiplication_mod_ops.

Module Export Hints.
  Import dettman_multiplication_mod_ops.
#[global]
  Hint Rewrite eval_mulmod using solve [ auto with zarith | congruence ] : push_eval.
#[global]
  Hint Rewrite eval_squaremod using solve [ auto with zarith | congruence ] : push_eval.
End Hints.
