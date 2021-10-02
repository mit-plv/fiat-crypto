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
  Proof using Type.
    rewrite !Z.ones_equiv; auto with zarith.
  Qed.
  Hint Resolve ones_le : zarith.

  Lemma ones_lt_pow2 x y : 0 <= x <= y -> Z.ones x < 2^y.
  Proof using Type.
    rewrite Z.ones_equiv, Z.lt_pred_le.
    auto with zarith.
  Qed.
  Hint Resolve ones_lt_pow2 : zarith.

  Lemma log2_ones_full x : Z.log2 (Z.ones x) = Z.max 0 (Z.pred x).
  Proof using Type.
    rewrite Z.ones_equiv, Z.log2_pred_pow2_full; reflexivity.
  Qed.
  Hint Rewrite log2_ones_full : zsimplify.

  Lemma log2_ones_lt x y : 0 < x <= y -> Z.log2 (Z.ones x) < y.
  Proof using Type.
    rewrite log2_ones_full; apply Z.max_case_strong; lia.
  Qed.
  Hint Resolve log2_ones_lt : zarith.

  Lemma log2_ones_le x y : 0 <= x <= y -> Z.log2 (Z.ones x) <= y.
  Proof using Type.
    rewrite log2_ones_full; apply Z.max_case_strong; lia.
  Qed.
  Hint Resolve log2_ones_le : zarith.

  Lemma log2_ones_lt_nonneg x y : 0 < y -> x <= y -> Z.log2 (Z.ones x) < y.
  Proof using Type.
    rewrite log2_ones_full; apply Z.max_case_strong; lia.
  Qed.
  Hint Resolve log2_ones_lt_nonneg : zarith.

  Lemma ones_pred : forall i, 0 < i -> Z.ones (Z.pred i) = Z.shiftr (Z.ones i) 1.
  Proof using Type.
    induction i as [|p|p]; [ | | pose proof (Pos2Z.neg_is_neg p) ]; try lia.
    intros.
    unfold Z.ones.
    rewrite !Z.shiftl_1_l, Z.shiftr_div_pow2, <-!Z.sub_1_r, Z.pow_1_r, <-!Z.add_opp_r by lia.
    replace (2 ^ (Z.pos p)) with (2 ^ (Z.pos p - 1)* 2).
    rewrite Z.div_add_l by lia.
    reflexivity.
    change 2 with (2 ^ 1) at 2.
    rewrite <-Z.pow_add_r by (pose proof (Pos2Z.is_pos p); lia).
    f_equal. lia.
  Qed.
  Hint Rewrite <- ones_pred using zutil_arith : push_Zshift.

  Lemma ones_succ : forall x, (0 <= x) ->
    Z.ones (Z.succ x) = 2 ^ x + Z.ones x.
  Proof using Type.
    unfold Z.ones; intros.
    rewrite !Z.shiftl_1_l.
    rewrite Z.add_pred_r.
    apply Z.succ_inj.
    rewrite !Z.succ_pred.
    rewrite Z.pow_succ_r; lia.
  Qed.

  Lemma ones_nonneg : forall i, (0 <= i) -> 0 <= Z.ones i.
  Proof using Type.
    apply natlike_ind.
    + unfold Z.ones. simpl; lia.
    + intros.
      rewrite Z.ones_succ by assumption.
      Z.zero_bounds.
  Qed.
  Hint Resolve ones_nonneg : zarith.

  Lemma ones_bound m (Hm : 0 <= m) :
    0 <= Z.ones m < 2 ^ m.
  Proof using Type. split. apply ones_nonneg; lia. rewrite Z.ones_equiv; lia. Qed.

  Lemma ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
  Proof using Type.
    intros.
    unfold Z.ones.
    rewrite Z.shiftl_1_l.
    apply Z.lt_succ_lt_pred.
    apply Z.pow_gt_1; lia.
  Qed.
  Hint Resolve ones_pos_pos : zarith.

  Lemma lnot_ones_equiv n : Z.lnot (Z.ones n) = -2^n.
  Proof using Type. rewrite Z.ones_equiv, Z.lnot_equiv, <- ?Z.sub_1_r; lia. Qed.

  Lemma land_ones_ones n m
    : Z.land (Z.ones n) (Z.ones m)
      = Z.ones (if ((n <? 0) || (m <? 0))
                then Z.max n m
                else Z.min n m).
  Proof using Type.
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
  Proof using Type.
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

  Lemma lor_pow2_mod_pow2_r x e (He : 0 <= e) : Z.lor x (2^e-1) mod (2^e) = 2^e-1.
  Proof using Type.
    destruct (Z_zerop e).
    { subst; autorewrite with zsimplify_const; reflexivity. }
    assert (0 <= x mod 2^e < 2^e) by auto with zarith.
    assert (0 <= x mod 2^e <= 2^e-1) by lia.
    assert (Z.log2 (x mod 2^e) <= Z.log2 (2^e-1)) by (apply Z.log2_le_mono; lia).
    assert (Z.log2 (x mod 2^e) < e) by (rewrite Z.sub_1_r, Z.log2_pred_pow2 in * by lia; lia).
    rewrite <- Z.land_ones, Z.land_lor_distr_l by assumption.
    rewrite !Z.sub_1_r, <- !Z.ones_equiv, !Z.land_ones_ones, Z.min_id, Z.max_id, Bool.if_const.
    rewrite Z.land_ones by assumption.
    rewrite Z.lor_ones_low; auto with zarith.
  Qed.
  Hint Rewrite lor_pow2_mod_pow2_r using zutil_arith : zsimplify.
  Hint Rewrite lor_pow2_mod_pow2_r using assumption : zsimplify_fast.

  Lemma lor_pow2_mod_pow2_l x e (He : 0 <= e) : Z.lor (2^e-1) x mod (2^e) = 2^e-1.
  Proof using Type. rewrite Z.lor_comm; apply lor_pow2_mod_pow2_r; assumption. Qed.
  Hint Rewrite lor_pow2_mod_pow2_l using zutil_arith : zsimplify.
  Hint Rewrite lor_pow2_mod_pow2_l using assumption : zsimplify_fast.

  Lemma lor_pow2_div_pow2_r x e (He : 0 <= e) : (Z.lor x (2^e-1)) / (2^e) = x / 2^e.
  Proof using Type.
    destruct (Z_zerop e).
    { subst; autorewrite with zsimplify_const; reflexivity. }
    assert (0 < 2^e) by auto with zarith.
    rewrite <- Z.shiftr_div_pow2, Z.shiftr_lor, !Z.shiftr_div_pow2 by lia.
    rewrite (Z.div_small (_-1) _), Z.lor_0_r by lia.
    reflexivity.
  Qed.
  Hint Rewrite lor_pow2_div_pow2_r using zutil_arith : zsimplify.
  Hint Rewrite lor_pow2_div_pow2_r using assumption : zsimplify_fast.

  Lemma lor_pow2_div_pow2_l x e (He : 0 <= e) : (Z.lor (2^e-1) x) / (2^e) = x / 2^e.
  Proof using Type. rewrite Z.lor_comm; apply lor_pow2_div_pow2_r; assumption. Qed.
  Hint Rewrite lor_pow2_div_pow2_l using zutil_arith : zsimplify.
  Hint Rewrite lor_pow2_div_pow2_l using assumption : zsimplify_fast.

  Lemma land_ones_low_alt a n : 0 <= a < 2^n -> Z.land a (Z.ones n) = a.
  Proof using Type.
    destruct (Z_zerop a); subst; [ intros; now rewrite Z.land_0_l | ].
    intros; apply Z.land_ones_low; try lia; apply Z.log2_lt_pow2; try lia.
  Qed.
  Hint Rewrite land_ones_low_alt using zutil_arith : zsimplify.
  Hint Rewrite land_ones_low_alt using (idtac + split); assumption : zsimplify_fast.

  Lemma land_ones_low_alt_ones a n : 0 <= a <= Z.ones n -> Z.land a (Z.ones n) = a.
  Proof using Type. rewrite Z.ones_equiv at 1; intro H; rewrite land_ones_low_alt; lia. Qed.
  Hint Rewrite land_ones_low_alt_ones using zutil_arith : zsimplify.
  Hint Rewrite land_ones_low_alt_ones using (idtac + split); assumption : zsimplify_fast.

  Lemma shiftr_ones_sub n m : 0 <= m <= n -> Z.shiftr (Z.ones n) m = Z.ones (n - m).
  Proof using Type. intro; now rewrite Z.shiftr_div_pow2, Z.ones_div_pow2 by lia. Qed.
  Hint Rewrite shiftr_ones_sub using zutil_arith : zsimplify.
  Hint Rewrite shiftr_ones_sub using (idtac + split); assumption : zsimplify_fast.

  Lemma shiftr_ones_same n : 0 <= n -> Z.shiftr (Z.ones n) n = 0.
  Proof using Type. intro; rewrite shiftr_ones_sub, Z.sub_diag by lia; reflexivity. Qed.
  Hint Rewrite shiftr_ones_same using zutil_arith : zsimplify.
  Hint Rewrite shiftr_ones_same using assumption : zsimplify_fast.
End Z.
