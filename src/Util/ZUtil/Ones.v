Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Pow2.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Lnot.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.ZSimplify.Simple.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma ones_le x y : x <= y -> Z.ones x <= Z.ones y.
  Proof.
    rewrite !Z.ones_equiv; auto with zarith.
  Qed.
  Hint Resolve ones_le : zarith.

  Lemma ones_lt_pow2 x y : 0 <= x <= y -> Z.ones x < 2^y.
  Proof.
    rewrite Z.ones_equiv, Z.lt_pred_le.
    auto with zarith.
  Qed.
  Hint Resolve ones_lt_pow2 : zarith.

  Lemma log2_ones_full x : Z.log2 (Z.ones x) = Z.max 0 (Z.pred x).
  Proof.
    rewrite Z.ones_equiv, Z.log2_pred_pow2_full; reflexivity.
  Qed.
  Hint Rewrite log2_ones_full : zsimplify.

  Lemma log2_ones_lt x y : 0 < x <= y -> Z.log2 (Z.ones x) < y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_lt : zarith.

  Lemma log2_ones_le x y : 0 <= x <= y -> Z.log2 (Z.ones x) <= y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_le : zarith.

  Lemma log2_ones_lt_nonneg x y : 0 < y -> x <= y -> Z.log2 (Z.ones x) < y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_lt_nonneg : zarith.

  Lemma ones_pred : forall i, 0 < i -> Z.ones (Z.pred i) = Z.shiftr (Z.ones i) 1.
  Proof.
    induction i as [|p|p]; [ | | pose proof (Pos2Z.neg_is_neg p) ]; try omega.
    intros.
    unfold Z.ones.
    rewrite !Z.shiftl_1_l, Z.shiftr_div_pow2, <-!Z.sub_1_r, Z.pow_1_r, <-!Z.add_opp_r by omega.
    replace (2 ^ (Z.pos p)) with (2 ^ (Z.pos p - 1)* 2).
    rewrite Z.div_add_l by omega.
    reflexivity.
    change 2 with (2 ^ 1) at 2.
    rewrite <-Z.pow_add_r by (pose proof (Pos2Z.is_pos p); omega).
    f_equal. omega.
  Qed.
  Hint Rewrite <- ones_pred using zutil_arith : push_Zshift.

  Lemma ones_succ : forall x, (0 <= x) ->
    Z.ones (Z.succ x) = 2 ^ x + Z.ones x.
  Proof.
    unfold Z.ones; intros.
    rewrite !Z.shiftl_1_l.
    rewrite Z.add_pred_r.
    apply Z.succ_inj.
    rewrite !Z.succ_pred.
    rewrite Z.pow_succ_r; omega.
  Qed.

  Lemma ones_nonneg : forall i, (0 <= i) -> 0 <= Z.ones i.
  Proof.
    apply natlike_ind.
    + unfold Z.ones. simpl; omega.
    + intros.
      rewrite Z.ones_succ by assumption.
      Z.zero_bounds.
  Qed.
  Hint Resolve ones_nonneg : zarith.

  Lemma ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
  Proof.
    intros.
    unfold Z.ones.
    rewrite Z.shiftl_1_l.
    apply Z.lt_succ_lt_pred.
    apply Z.pow_gt_1; omega.
  Qed.
  Hint Resolve ones_pos_pos : zarith.

  Lemma lnot_ones_equiv n : Z.lnot (Z.ones n) = -2^n.
  Proof. rewrite Z.ones_equiv, Z.lnot_equiv, <- ?Z.sub_1_r; lia. Qed.

  Lemma land_ones_ones n m
    : Z.land (Z.ones n) (Z.ones m)
      = Z.ones (if ((n <? 0) || (m <? 0))
                then Z.max n m
                else Z.min n m).
  Proof.
    repeat first [ reflexivity
                 | break_innermost_match_step
                 | progress rewrite ?Bool.orb_true_iff in *
                 | progress rewrite ?Bool.orb_false_iff in *
                 | progress rewrite ?Z.ltb_lt, ?Z.ltb_ge in *
                 | progress destruct_head'_and
                 | apply Z.min_case_strong
                 | apply Z.max_case_strong
                 | progress intros
                 | progress destruct_head'_or
                 | rewrite !Z.pow_r_Zneg
                 | rewrite !Z.land_m1_l
                 | rewrite !Z.land_m1_r
                 | progress change (Z.pred 0) with (-1)
                 | rewrite Z.mod_small by lia
                 | match goal with
                   | [ H : ?x < 0 |- _ ] => is_var x; destruct x; try lia
                   | [ H : ?x <= Z.neg _ |- _ ] => is_var x; destruct x; try lia
                   | [ |- context[Z.ones (Z.neg ?x)] ] => rewrite (Z.ones_equiv (Z.neg x))
                   | [ H : ?n <= ?m |- Z.land (Z.ones ?m) (Z.ones ?n) = _ ]
                     => rewrite (Z.land_comm (Z.ones m) (Z.ones n))
                   | [ H : ?n <= ?m |- Z.land (Z.ones ?n) (Z.ones ?m) = _ ]
                     => progress rewrite ?Z.land_ones, ?Z.ones_equiv, <- ?Z.sub_1_r by auto
                   | [ H : ?n <= ?m |- _ ]
                     => is_var n; is_var m; unique pose proof (Z.pow_le_mono_r 2 n m ltac:(lia) H)
                   | [ |- context[2^?x] ] => unique pose proof (Z.pow2_gt_0 x ltac:(lia))
                   end ].
  Qed.
  Hint Rewrite land_ones_ones : zsimplify.

  Lemma lor_ones_ones n m
    : Z.lor (Z.ones n) (Z.ones m)
      = Z.ones (if ((n <? 0) || (m <? 0))
                then Z.min n m
                else Z.max n m).
  Proof.
    destruct (Z_zerop n), (Z_zerop m); subst;
      repeat first [ reflexivity
                   | break_innermost_match_step
                   | progress rewrite ?Bool.orb_true_iff in *
                   | progress rewrite ?Bool.orb_false_iff in *
                   | progress rewrite ?Z.ltb_lt, ?Z.ltb_ge in *
                   | progress destruct_head'_and
                   | apply Z.min_case_strong
                   | apply Z.max_case_strong
                   | progress intros
                   | progress destruct_head'_or
                   | rewrite !Z.pow_r_Zneg
                   | rewrite !Z.lor_m1_l
                   | rewrite !Z.lor_m1_r
                   | progress change (Z.pred 0) with (-1)
                   | rewrite Z.mod_small by lia
                   | lia
                   | match goal with
                     | [ H : ?x < 0 |- _ ] => is_var x; destruct x; try lia
                     | [ H : ?x <= Z.neg _ |- _ ] => is_var x; destruct x; try lia
                     | [ |- context[Z.ones (Z.neg ?x)] ] => rewrite (Z.ones_equiv (Z.neg x))
                     | [ H : ?n <= ?m |- Z.lor (Z.ones ?m) (Z.ones ?n) = _ ]
                       => rewrite (Z.lor_comm (Z.ones m) (Z.ones n))
                     | [ H : ?n <= ?m |- Z.lor (Z.ones ?n) (Z.ones ?m) = _ ]
                       => progress rewrite ?Z.lor_ones_low; try apply Z.log2_ones_lt_nonneg; rewrite ?Z.ones_equiv, <- ?Z.sub_1_r
                     | [ H : ?n <= ?m |- _ ]
                       => is_var n; is_var m; unique pose proof (Z.pow_le_mono_r 2 n m ltac:(lia) H)
                     | [ |- context[2^?x] ] => unique pose proof (Z.pow2_gt_0 x ltac:(lia))
                     end ].
  Qed.
  Hint Rewrite lor_ones_ones : zsimplify.
End Z.
