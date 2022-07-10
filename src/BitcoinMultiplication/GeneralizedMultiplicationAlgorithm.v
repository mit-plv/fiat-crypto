Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.NatInt.NZPow.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Require Import Coq.Numbers.NatInt.NZDiv.
(** * Push-Button Synthesis Examples *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.BitcoinMultiplication.HelpfulFunctions.
Require Import Crypto.BitcoinMultiplication.OriginalMultiplicationAlgorithm.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional HelpfulFunctions.
Import ListNotations. Local Open Scope Z_scope.

Notation "a ** b" := (Zpower_nat a b)
  (at level 41, right associativity).

Section Stuff.

Context
        (e : nat)
        (c : Z)
        (p_nz : 2 ** e - c <> 0)
        (limbs : nat)
        (limb_size : nat)
        (limbs_gteq_3 : (limbs >= 3)%nat)
        (e_small : (e <= limb_size * limbs)%nat)
        (e_big : (limb_size * (limbs - 1) <= e)%nat).

Let s := (2 ** e).

Let base := (2 ** limb_size).

Lemma base_nz : base <> 0.
Proof. cbv [base]. rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia. Qed.

Lemma s_nz : s <> 0.
Proof. cbv [s]. rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia. Qed.

Let weight n : Z := base ** n.

Lemma weight_0 : weight 0 = 1.
Proof. reflexivity. Qed.

Lemma weight_nz : forall i, weight i <> 0.
Proof.
  intros i. cbv [weight]. rewrite Zpower_nat_Z. apply Z.pow_nonzero.
  - apply base_nz.
  - lia.
Qed.

Lemma mod_is_zero : forall b (n m : nat), b <> 0 -> le n m -> (b ** m) mod (b ** n) = 0.
  intros b n m H1 H2. induction H2.
  - rewrite Z_mod_same_full. constructor.
  - rewrite Zpower_nat_succ_r. rewrite Z.mul_mod_full. rewrite IHle. rewrite Z.mul_0_r.
    apply Z.mod_0_l. rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia.
Qed.

Check Z_div_le.

Lemma div_nz a b : b > 0 -> b <= a -> a / b <> 0.
Proof.
  intros H1 H2. assert (1 <= a / b).
  - replace 1 with (b / b).
    + apply Z_div_le.
      -- apply H1.
      -- apply H2.
    + apply Z_div_same. apply H1.
  - symmetry. apply Z.lt_neq. apply Z.lt_le_trans with 1.
    + reflexivity.
    + apply H.
Qed.

Lemma pow_mul x y z : (x ** y) ** z = x ** (y * z).
Proof.
  repeat rewrite Zpower_nat_Z. rewrite Nat2Z.inj_mul. rewrite Z.pow_mul_r.
  - reflexivity.
  - apply Zle_0_nat.
  - apply Zle_0_nat.
Qed.

Lemma limbs_mod_s_0 : (weight limbs) mod s = 0.
Proof.
  cbv [weight base s]. rewrite pow_mul. apply mod_is_zero.
  - lia.
  - apply e_small.
Qed.

Local Open Scope nat_scope.

(* want to start with i = 1 (up to l - 2, excludsive), so want to start with l_minus_2_minus_i = l - 2 - 1 *)
Fixpoint loop l weight s c l_minus_2_minus_i r0 :=
  match l_minus_2_minus_i with
  | O => r0
  | S l_minus_2_minus_i' =>
    let i := (l - 2) - l_minus_2_minus_i in
    let r1 := Associational.carry (weight (i + l)) (weight 1) r0 in
    let r2 := reduce_one s (weight (i + l)) (weight l) c r1 in
    let r3 := Associational.carry (weight i) (weight 1) r2 in
    loop l weight s c l_minus_2_minus_i' r3
  end.

Definition reduce' x1 x2 x3 x4 x5 := collect_terms (reduce_one x1 x2 x3 x4 x5).
Definition carry' x1 x2 x3 := collect_terms (Associational.carry x1 x2 x3).

Definition loop_body i before :=
  let middle1 := carry' (weight (i + limbs)) (weight 1) before in
  let middle2 := reduce' s (weight (i + limbs)) (weight limbs) c middle1 in
  let after := carry' (weight i) (weight 1) middle2 in
  after.

Lemma eval_loop_body i before :
  (Associational.eval (loop_body i before) mod (s - c) =
  Associational.eval before mod (s - c))%Z.
Proof.
  cbv [loop_body carry' reduce'].
  repeat (try rewrite eval_reduce_one;
          try rewrite Associational.eval_carry;
          try rewrite eval_collect_terms).
  reflexivity.
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

Compute (from_n_to_one 2).

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
  let r0' := collect_terms r0 in
  let r1 := carry' (weight (2 * l - 2)) (weight 1) r0' in
  let r2 := reduce' s (weight (2 * l - 2)) (weight l) c r1 in
  let r3 := carry' (weight (l - 2)) (weight 1) r2 in
  let r4 := reduce' s (weight (2 * l - 1)) (weight l) c r3 in
  let r5 := carry' (weight (l - 1)) (weight 1) r4 in
  let r6 := carry' (weight l) (weight 1) r5 in
  let r7 := carry_down (weight l) (weight l / s) r6 in
  let r7' := collect_terms r7 in
  let r8 := carry' (weight (l - 1)) (Z.div s (weight (l - 1))) r7' in
  let r9 := reduce' s s s c r8 in
  let r10 := carry' (weight 0) (weight 1) r9 in
  let r11 := loop' r10 in
  let r12 := reduce' s (weight (2 * l - 2)) (weight l) c r11 in
  let r13 := carry' (weight (l - 2)) (weight 1) r12 in
  Positional.from_associational weight l r13.

Local Open Scope Z_scope.

Theorem eval_mulmod_general a b :
  (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c) =
  (Positional.eval weight limbs (mulmod_general a b)) mod (s - c).
Proof.
  cbv [mulmod_general carry' reduce'].
  repeat (try rewrite Positional.eval_from_associational;
          try rewrite Positional.eval_to_associational;
          try rewrite Associational.eval_carry;
          try rewrite eval_reduce_one;
          try rewrite eval_carry_down;
          try rewrite eval_collect_terms;
          try rewrite eval_loop').
  rewrite Associational.eval_mul. repeat rewrite Positional.eval_to_associational. reflexivity.
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
  - apply div_nz.
    + rewrite Zpower_nat_Z. lia.
    + rewrite pow_mul. repeat rewrite Zpower_nat_Z. rewrite Nat2Z.inj_mul. rewrite <- Z.pow_le_mono_r_iff.
      -- remember e_small as H. lia.
      -- lia.
      -- lia.
  - repeat rewrite pow_mul. Search (_ mod (_ / _)). repeat rewrite Zpower_nat_Z.
    rewrite <- Z.pow_sub_r.
    + rewrite <- Nat2Z.inj_sub. repeat rewrite <- Zpower_nat_Z. apply mod_is_zero.
      -- lia.
      -- lia.
      -- apply e_small.
    + lia.
    + remember e_small as H. lia.
  - apply div_nz.
    + repeat rewrite Zpower_nat_Z. lia.
    + rewrite pow_mul. repeat rewrite Zpower_nat_Z. rewrite Nat2Z.inj_mul. rewrite <- Z.pow_le_mono_r_iff.
      -- remember e_big as H. lia.
      -- lia.
      -- lia.
Qed.

End Stuff.
