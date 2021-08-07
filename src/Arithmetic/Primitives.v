Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs. (* For MontgomeryReduction *)
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tuple Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.ZUtil.Definitions.
Import Coq.Lists.List ListNotations. Local Open Scope Z_scope.

Section primitives.
  Definition mulx (bitwidth : Z) := Eval cbv [Z.mul_split_at_bitwidth] in Z.mul_split_at_bitwidth bitwidth.
  Definition addcarryx (bitwidth : Z) := Eval cbv [Z.add_with_get_carry Z.add_with_carry Z.get_carry] in Z.add_with_get_carry bitwidth.
  Definition subborrowx (bitwidth : Z) := Eval cbv [Z.sub_with_get_borrow Z.sub_with_borrow Z.get_borrow Z.get_carry Z.add_with_carry] in Z.sub_with_get_borrow bitwidth.
  Definition cmovznz_common (bitwidth : Z) (t : Z) (z nz : Z)
    := Z.lor (Z.land (Z.value_barrier t) nz) (Z.land (Z.value_barrier (Z.lnot_modulo t (2^bitwidth))) z).
  Definition cmovznz (bitwidth : Z) (cond : Z) (z nz : Z)
    := dlet t := (0 - Z.bneg (Z.bneg cond)) mod 2^bitwidth in cmovznz_common bitwidth t z nz.
  Definition cmovznz_by_mul (bitwidth : Z) (cond : Z) (z nz : Z)
    := dlet t := cond * (2^bitwidth - 1) in cmovznz_common bitwidth t z nz.

  Lemma mulx_correct (bitwidth : Z)
        (x y : Z)
    : mulx bitwidth x y = ((x * y) mod 2^bitwidth, (x * y) / 2^bitwidth).
  Proof using Type.
    change mulx with Z.mul_split_at_bitwidth.
    rewrite <- Z.mul_split_at_bitwidth_div, <- Z.mul_split_at_bitwidth_mod; eta_expand.
    eta_expand; reflexivity.
  Qed.

  Lemma addcarryx_correct (bitwidth : Z)
        (c x y : Z)
    : addcarryx bitwidth c x y = ((c + x + y) mod 2^bitwidth, (c + x + y) / 2^bitwidth).
  Proof using Type.
    cbv [addcarryx Let_In]; reflexivity.
  Qed.

  Lemma subborrowx_correct (bitwidth : Z)
        (b x y : Z)
    : subborrowx bitwidth b x y = ((-b + x + -y) mod 2^bitwidth, -((-b + x + -y) / 2^bitwidth)).
  Proof using Type.
    cbv [subborrowx Let_In]; reflexivity.
  Qed.

  Lemma cmovznz_correct bitwidth cond z nz
    : 0 <= z < 2^bitwidth
      -> 0 <= nz < 2^bitwidth
      -> cmovznz bitwidth cond z nz = Z.zselect cond z nz.
  Proof using Type.
    intros.
    assert (0 < 2^bitwidth) by lia.
    assert (0 <= bitwidth) by auto with zarith.
    assert (0 < bitwidth -> 1 < 2^bitwidth) by auto with zarith.
    pose proof Z.log2_lt_pow2_alt.
    assert (bitwidth = 0 \/ 0 < bitwidth) by lia.
    repeat first [ progress cbv [cmovznz cmovznz_common Z.zselect Z.bneg Let_In Z.lnot_modulo]
                 | progress split_iff
                 | progress subst
                 | progress Z.ltb_to_lt
                 | progress destruct_head'_or
                 | congruence
                 | lia
                 | progress break_innermost_match_step
                 | progress break_innermost_match_hyps_step
                 | progress autorewrite with zsimplify_const in *
                 | progress pull_Zmod
                 | progress intros
                 | rewrite !Z.sub_1_r, <- Z.ones_equiv, <- ?Z.sub_1_r
                 | rewrite Z_mod_nz_opp_full by (Z.rewrite_mod_small; lia)
                 | rewrite (Z.land_comm (Z.ones _))
                 | rewrite Z.land_ones_low by auto with lia
                 | progress Z.rewrite_mod_small ].
  Qed.

  Lemma cmovznz_by_mul_correct bitwidth cond z nz
    : 0 <= cond < 2^1
      -> 0 <= z < 2^bitwidth
      -> 0 <= nz < 2^bitwidth
      -> cmovznz_by_mul bitwidth cond z nz = Z.zselect cond z nz.
  Proof using Type.
    intros.
    assert (0 < 2^bitwidth) by lia.
    assert (0 <= bitwidth) by auto with zarith.
    assert (0 < bitwidth -> 1 < 2^bitwidth) by auto with zarith.
    pose proof Z.log2_lt_pow2_alt.
    assert (bitwidth = 0 \/ 0 < bitwidth) by lia.
    assert (cond = 0 \/ cond = 1) by lia.
    repeat first [ progress cbv [cmovznz_by_mul cmovznz_common Z.zselect Let_In Z.lnot_modulo Z.lnot Z.pred]
                 | progress split_iff
                 | progress subst
                 | progress Z.ltb_to_lt
                 | progress destruct_head'_or
                 | congruence
                 | lia
                 | progress break_innermost_match_step
                 | progress break_innermost_match_hyps_step
                 | progress autorewrite with zsimplify_const in *
                 | progress (push_Zmod; pull_Zmod)
                 | progress intros
                 | rewrite !Z.sub_1_r, <- Z.ones_equiv, <- ?Z.sub_1_r
                 | rewrite Z_mod_nz_opp_full by (Z.rewrite_mod_small; lia)
                 | rewrite (Z.land_comm (Z.ones _))
                 | rewrite Z.land_ones_low by auto with lia
                 | progress Z.rewrite_mod_small
                 | replace (-Z.ones bitwidth + -1) with (-2^bitwidth) by (rewrite Z.ones_equiv, <- Z.sub_1_r; lia) ].
  Qed.
End primitives.
