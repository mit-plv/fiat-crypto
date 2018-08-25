Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Pow2.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.Lnot.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Lemma round_lor_land_bound_bounds x
  : (0 <= x <= Z.round_lor_land_bound x) \/ (Z.round_lor_land_bound x <= x <= -1).
  Proof.
    cbv [Z.round_lor_land_bound]; break_innermost_match; Z.ltb_to_lt.
    all: constructor; split; try lia; [].
    all: Z.replace_all_neg_with_pos.
    all: match goal with |- context[2^Z.log2_up ?x] => pose proof (Z.log2_up_le_full x) end.
    all: lia.
  Qed.
  Hint Resolve round_lor_land_bound_bounds : zarith.

  Lemma round_lor_land_bound_bounds_pos x
  : (0 <= Z.pos x <= Z.round_lor_land_bound (Z.pos x)).
  Proof. generalize (round_lor_land_bound_bounds (Z.pos x)); lia. Qed.
  Hint Resolve round_lor_land_bound_bounds_pos : zarith.

  Lemma round_lor_land_bound_bounds_neg x
  : Z.round_lor_land_bound (Z.neg x) <= Z.neg x <= -1.
  Proof. generalize (round_lor_land_bound_bounds (Z.neg x)); lia. Qed.
  Hint Resolve round_lor_land_bound_bounds_neg : zarith.

  Local Ltac saturate :=
    repeat first [ progress cbv [Z.round_lor_land_bound Proper respectful Basics.flip] in *
                 | progress Z.ltb_to_lt
                 | progress intros
                 | break_innermost_match_step
                 | lia
                 | rewrite !Pos2Z.opp_neg
                 | match goal with
                   | [ |- context[Z.log2_up ?x] ]
                     => unique pose proof (Z.log2_up_nonneg x)
                   | [ |- context[2^?x] ]
                     => unique assert (0 <= 2^x) by (apply Z.pow_nonneg; lia)
                   | [ H : 0 <= ?x |- context[2^?x] ]
                     => unique assert (0 < 2^x) by (apply Z.pow_pos_nonneg; lia)
                   | [ H : Pos.le ?x ?y |- context[Z.pos ?x] ]
                     => unique assert (Z.pos x <= Z.pos y) by lia
                   | [ H : Pos.le ?x ?y |- context[Z.pos (?x+1)] ]
                     => unique assert (Z.pos (x+1) <= Z.pos (y+1)) by lia
                   | [ H : Z.le ?x ?y |- context[?x+1] ]
                     => unique assert (x+1 <= y+1) by lia
                   | [ H : Z.le ?x ?y |- context[2^Z.log2_up ?x] ]
                     => unique assert (2^Z.log2_up x <= 2^Z.log2_up y) by (Z.peel_le; lia)
                   | [ H : ?a^?b <= ?a^?c |- _ ]
                     => unique assert (a^(c-b) = a^c/a^b) by auto with zarith;
                       unique assert (a^c mod a^b = 0) by auto with zarith
                   end ].
  Local Ltac do_rewrites_step :=
    match goal with
    | [ |- ?R ?x ?x ] => reflexivity
    (*| [ |- context[Z.land (-2^_) (-2^_)] ]
      => rewrite <- !Z.lnot_ones_equiv, <- !Z.lnot_lor, !Z.lor_ones_ones, !Z.lnot_ones_equiv
    | [ |- context[Z.lor (-2^_) (-2^_)] ]
      => rewrite <- !Z.lnot_ones_equiv, <- !Z.lnot_land, !Z.land_ones_ones, !Z.lnot_ones_equiv
    | [ |- context[Z.land (2^_-1) (2^_-1)] ]
      => rewrite !Z.sub_1_r, <- !Z.ones_equiv, !Z.land_ones_ones, !Z.ones_equiv, <- !Z.sub_1_r
    | [ |- context[Z.lor (2^_-1) (2^_-1)] ]
      => rewrite !Z.sub_1_r, <- !Z.ones_equiv, !Z.lor_ones_ones, !Z.ones_equiv, <- !Z.sub_1_r
    | [ |- context[Z.land (2^?x-1) (-2^?y)] ]
      => rewrite (@Z.land_comm (2^x-1) (-2^y))
    | [ |- context[Z.lor (2^?x-1) (-2^?y)] ]
      => rewrite (@Z.lor_comm (2^x-1) (-2^y))
    | [ |- context[Z.land (-2^_) (2^_-1)] ]
      => rewrite !Z.sub_1_r, <- !Z.ones_equiv, !Z.land_ones, ?Z.ones_equiv, <- ?Z.sub_1_r by lia
    | [ |- context[Z.lor (-2^?x) (2^?y-1)] ]
      => rewrite <- !Z.lnot_ones_equiv, <- (Z.lnot_involutive (2^y-1)), <- !Z.lnot_land, ?Z.lnot_ones_equiv, (Z.lnot_sub1 (2^y)), !Z.ones_equiv, ?Z.lnot_equiv, <- !Z.sub_1_r
    | [ |- context[-?x mod ?y] ]
      => rewrite (@Z.opp_mod_mod_push x y) by Z.NoZMod*)
    | [ |- context[Z.land (2^?y-1) ?x] ]
      => is_var x; rewrite (Z.land_comm (2^y-1) x)
    | [ |- context[Z.lor (2^?y-1) ?x] ]
      => is_var x; rewrite (Z.lor_comm (2^y-1) x)
    | [ |- context[Z.land (-2^?y) ?x] ]
      => is_var x; rewrite (Z.land_comm (-2^y) x)
    | [ |- context[Z.lor (-2^?y) ?x] ]
      => is_var x; rewrite (Z.lor_comm (-2^y) x)
    | [ |- context[Z.land _ (2^_-1)] ]
      => rewrite !Z.sub_1_r, <- !Z.ones_equiv, !Z.land_ones by auto with zarith
    | [ |- context[Z.land ?x (-2^?y)] ]
      => is_var x;
        rewrite <- !Z.lnot_ones_equiv, <- (Z.lnot_involutive x), <- !Z.lnot_lor, !Z.ones_equiv, !Z.lnot_equiv, <- !Z.sub_1_r;
        let x' := fresh in
        remember (-x-1) as x' eqn:?; Z.linear_substitute x;
        rename x' into x
    | [ |- context[Z.lor ?x (-2^?y)] ]
      => is_var x;
        rewrite <- !Z.lnot_ones_equiv, <- (Z.lnot_involutive x), <- !Z.lnot_land, !Z.ones_equiv, !Z.lnot_equiv, <- !Z.sub_1_r;
        let x' := fresh in
        remember (-x-1) as x' eqn:?; Z.linear_substitute x;
        rename x' into x
    | [ |- Z.lor ?x (?y-1) <= Z.lor ?x (?y'-1) ]
      => rewrite (Z.div_mod'' (Z.lor x (y-1)) y), (Z.div_mod'' (Z.lor x (y'-1)) y') by auto with zarith
    | [ |- Z.lor ?x (?y-1) = _ ]
      => rewrite (Z.div_mod'' (Z.lor x (y-1)) y) by auto with zarith
    | [ |- context[?m1 - 1 + (?x - ?x mod ?m1)] ]
      => replace (m1 - 1 + (x - x mod m1)) with ((m1 - x mod m1) + (x - 1)) by lia
    | _ => progress rewrite ?Z.lor_pow2_div_pow2_r, ?Z.lor_pow2_div_pow2_l, ?Z.lor_pow2_mod_pow2_r, ?Z.lor_pow2_mod_pow2_l by auto with zarith
    | _ => rewrite !Z.mul_div_eq by lia
    | _ => progress rewrite ?(Z.add_comm 1) in *
    | [ |- context[?x mod 2^(Z.log2_up (?x + 1))] ]
      => rewrite (Z.mod_small x (2^Z.log2_up (x+1))) by (rewrite <- Z.le_succ_l, <- Z.add_1_r, Z.log2_up_le_pow2 by lia; lia)
    | [ H : ?a^?b <= ?a^?c |- context[?x mod ?a^?b] ]
      => rewrite (@Z.mod_pow_r_split x a b c) by auto with zarith;
        (Z.div_mod_to_quot_rem; nia)
    | _ => progress Z.peel_le
    (*| [ H : ?x <= ?x |- _ ] => clear H
    | [ H : ?x < ?y, H' : ?y <= ?z |- _ ] => unique assert (x < z) by lia
    | [ H : ?x < ?y, H' : ?a <= ?x |- _ ] => unique assert (a < y) by lia
    | [ H : 2^?x < 2^?y |- context[2^?x mod 2^?y] ]
      => repeat first [ rewrite (Z.mod_small (2^x) (2^y)) by lia
                      | rewrite !(@Z_mod_nz_opp_full (2^x) (2^y)) ]
    | [ H : ?x < ?y, H' : context[?x mod ?y] |- _ ] => rewrite (Z.mod_small x y) in H' by lia
    | [ |- context[2^?x mod 2^?y] ]
      => let H := fresh in
         destruct (@Z.pow2_lt_or_divides x y ltac:(lia)) as [H|H];
         [ repeat first [ rewrite (Z.mod_small (2^x) (2^y)) by lia
                        | rewrite !(@Z_mod_nz_opp_full (2^x) (2^y)) ]
         | rewrite H ]*)
    | _ => progress autorewrite with zsimplify_fast in *
    | [ |- context[-(-?x-1)] ] => replace (-(-x-1)) with (1+x) by lia
    | [ H : 0 > -(1+?x) |- _ ] => assert (0 <= x) by (clear -H; lia); clear H
    | [ H : 0 > -(?x+1) |- _ ] => assert (0 <= x) by (clear -H; lia); clear H
    | [ |- ?a - ?b = ?a' - ?b' ] => apply f_equal2; try reflexivity; []
    | [ |- -?a = -?a' ] => apply f_equal
    | _ => rewrite <- !Z.sub_1_r
    | _ => lia
    end.
  Local Ltac do_rewrites := repeat do_rewrites_step.
  Local Ltac fin_t :=
    repeat first [ progress destruct_head'_and
                 | match goal with
                   | [ H : orb _ _ = _ |- _ ]
                     => progress rewrite ?Bool.orb_true_iff, ?Bool.orb_false_iff, ?Z.ltb_lt, ?Z.ltb_ge in *
                   end
                 | break_innermost_match_step
                 | progress destruct_head'_or
                 | lia
                 | progress Z.peel_le ].
  Local Ltac t :=
    saturate; do_rewrites.

  Local Instance land_round_Proper_pos_r x
    : Proper (Pos.le ==> Z.le) (fun y => Z.land x (Z.round_lor_land_bound (Z.pos y))).
  Proof. t. Qed.

  Local Instance land_round_Proper_pos_l y
    : Proper (Pos.le ==> Z.le) (fun x => Z.land (Z.round_lor_land_bound (Z.pos x)) y).
  Proof. t. Qed.

  Local Instance lor_round_Proper_pos_r x
    : Proper (Pos.le ==> Z.le) (fun y => Z.lor x (Z.round_lor_land_bound (Z.pos y))).
  Proof. t. Qed.

  Local Instance lor_round_Proper_pos_l y
    : Proper (Pos.le ==> Z.le) (fun x => Z.lor (Z.round_lor_land_bound (Z.pos x)) y).
  Proof. t. Qed.

  Local Instance land_round_Proper_neg_r x
    : Proper (Basics.flip Pos.le ==> Z.le) (fun y => Z.land x (Z.round_lor_land_bound (Z.neg y))).
  Proof. t. Qed.

  Local Instance land_round_Proper_neg_l y
    : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.land (Z.round_lor_land_bound (Z.neg x)) y).
  Proof. t. Qed.

  Local Instance lor_round_Proper_neg_r x
    : Proper (Basics.flip Pos.le ==> Z.le) (fun y => Z.lor x (Z.round_lor_land_bound (Z.neg y))).
  Proof. t. Qed.

  Local Instance lor_round_Proper_neg_l y
    : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.lor (Z.round_lor_land_bound (Z.neg x)) y).
  Proof. t. Qed.

  Lemma land_round_lor_land_bound_r x
    : Z.land x (Z.round_lor_land_bound x) = if (0 <=? x) then x else Z.round_lor_land_bound x.
  Proof. t. Qed.
  Hint Rewrite land_round_lor_land_bound_r : zsimplify_fast zsimplify.
  Lemma land_round_lor_land_bound_l x
    : Z.land (Z.round_lor_land_bound x) x = if (0 <=? x) then x else Z.round_lor_land_bound x.
  Proof. rewrite Z.land_comm, land_round_lor_land_bound_r; reflexivity. Qed.
  Hint Rewrite land_round_lor_land_bound_l : zsimplify_fast zsimplify.

  Lemma lor_round_lor_land_bound_r x
    : Z.lor x (Z.round_lor_land_bound x) = if (0 <=? x) then Z.round_lor_land_bound x else x.
  Proof. t. Qed.
  Hint Rewrite lor_round_lor_land_bound_r : zsimplify_fast zsimplify.
  Lemma lor_round_lor_land_bound_l x
    : Z.lor (Z.round_lor_land_bound x) x = if (0 <=? x) then Z.round_lor_land_bound x else x.
  Proof. rewrite Z.lor_comm, lor_round_lor_land_bound_r; reflexivity. Qed.
  Hint Rewrite lor_round_lor_land_bound_l : zsimplify_fast zsimplify.

  Lemma land_round_bound_pos_r v x
    : 0 <= Z.land v (Z.pos x) <= Z.land v (Z.round_lor_land_bound (Z.pos x)).
  Proof.
    rewrite Z.land_nonneg; split; [ lia | ].
    replace (Z.pos x) with (Z.land (Z.pos x) (Z.round_lor_land_bound (Z.pos x))) at 1
      by now rewrite land_round_lor_land_bound_r.
    rewrite (Z.land_comm (Z.pos x)), Z.land_assoc.
    apply Z.land_upper_bound_l; rewrite ?Z.land_nonneg; t.
  Qed.
  Hint Resolve land_round_bound_pos_r (fun v x => proj1 (land_round_bound_pos_r v x)) (fun v x => proj2 (land_round_bound_pos_r v x)) : zarith.
  Lemma land_round_bound_pos_l v x
    : 0 <= Z.land (Z.pos x) v <= Z.land (Z.round_lor_land_bound (Z.pos x)) v.
  Proof. rewrite <- !(Z.land_comm v); apply land_round_bound_pos_r. Qed.
  Hint Resolve land_round_bound_pos_l (fun v x => proj1 (land_round_bound_pos_l v x)) (fun v x => proj2 (land_round_bound_pos_l v x)) : zarith.

  Lemma land_round_bound_neg_r v x
    : Z.land v (Z.round_lor_land_bound (Z.neg x)) <= Z.land v (Z.neg x) <= v.
  Proof.
    assert (0 < 2 ^ Z.log2_up (Z.pos x)) by auto with zarith.
    split; [ | apply Z.land_le; lia ].
    replace (Z.round_lor_land_bound (Z.neg x)) with (Z.land (Z.neg x) (Z.round_lor_land_bound (Z.neg x)))
      by now rewrite land_round_lor_land_bound_r.
    rewrite !Z.land_assoc.
    etransitivity; [ apply Z.land_le; cbn; lia | ]; lia.
  Qed.
  Hint Resolve land_round_bound_neg_r (fun v x => proj1 (land_round_bound_neg_r v x)) (fun v x => proj2 (land_round_bound_neg_r v x)) : zarith.
  Lemma land_round_bound_neg_l v x
    : Z.land (Z.round_lor_land_bound (Z.neg x)) v <= Z.land (Z.neg x) v <= v.
  Proof. rewrite <- !(Z.land_comm v); apply land_round_bound_neg_r. Qed.
  Hint Resolve land_round_bound_neg_l (fun v x => proj1 (land_round_bound_neg_l v x)) (fun v x => proj2 (land_round_bound_neg_l v x)) : zarith.

  Lemma lor_round_bound_neg_r v x
    : Z.lor v (Z.round_lor_land_bound (Z.neg x)) <= Z.lor v (Z.neg x) <= -1.
  Proof.
    change (-1) with (Z.pred 0); rewrite <- Z.lt_le_pred.
    rewrite Z.lor_neg; split; [ | lia ].
    replace (Z.neg x) with (Z.lor (Z.neg x) (Z.round_lor_land_bound (Z.neg x))) at 2
      by now rewrite lor_round_lor_land_bound_r.
    rewrite (Z.lor_comm (Z.neg x)), Z.lor_assoc.
    cbn; rewrite <- !Z.lnot_ones_equiv, <- (Z.lnot_involutive v), <- (Z.lnot_involutive (Z.neg x)), <- !Z.lnot_land, !Z.ones_equiv, !Z.lnot_equiv, <- !Z.sub_1_r, !Pos2Z.opp_neg.
    Z.peel_le.
    apply Z.land_upper_bound_l; rewrite ?Z.land_nonneg; t.
  Qed.
  Hint Resolve lor_round_bound_neg_r (fun v x => proj1 (lor_round_bound_neg_r v x)) (fun v x => proj2 (lor_round_bound_neg_r v x)) : zarith.
  Lemma lor_round_bound_neg_l v x
    : Z.lor (Z.round_lor_land_bound (Z.neg x)) v <= Z.lor (Z.neg x) v <= -1.
  Proof. rewrite <- !(Z.lor_comm v); apply lor_round_bound_neg_r. Qed.
  Hint Resolve lor_round_bound_neg_l (fun v x => proj1 (lor_round_bound_neg_l v x)) (fun v x => proj2 (lor_round_bound_neg_l v x)) : zarith.

  Lemma lor_round_bound_pos_r v x
    : v <= Z.lor v (Z.pos x) <= Z.lor v (Z.round_lor_land_bound (Z.pos x)).
  Proof.
    assert (0 < 2 ^ Z.log2_up (Z.pos (x + 1))) by auto with zarith.
    split; [ apply Z.lor_lower; lia | ].
    replace (Z.round_lor_land_bound (Z.pos x)) with (Z.lor (Z.pos x) (Z.round_lor_land_bound (Z.pos x)))
      by now rewrite lor_round_lor_land_bound_r.
    rewrite !Z.lor_assoc.
    etransitivity; [ | apply Z.lor_lower; rewrite ?Z.lor_nonneg; cbn; lia ]; lia.
  Qed.
  Hint Resolve lor_round_bound_pos_r (fun v x => proj1 (lor_round_bound_pos_r v x)) (fun v x => proj2 (lor_round_bound_pos_r v x)) : zarith.
  Lemma lor_round_bound_pos_l v x
    : v <= Z.lor (Z.pos x) v <= Z.lor (Z.round_lor_land_bound (Z.pos x)) v.
  Proof. rewrite <- !(Z.lor_comm v); apply lor_round_bound_pos_r. Qed.
  Hint Resolve lor_round_bound_pos_l (fun v x => proj1 (lor_round_bound_pos_l v x)) (fun v x => proj2 (lor_round_bound_pos_l v x)) : zarith.

  Lemma land_round_bound_pos_r' v x : Z.land v (Z.pos x) <= Z.land v (Z.round_lor_land_bound (Z.pos x)). Proof. auto with zarith. Qed.
  Lemma land_round_bound_pos_l' v x : Z.land (Z.pos x) v <= Z.land (Z.round_lor_land_bound (Z.pos x)) v. Proof. auto with zarith. Qed.
  Lemma land_round_bound_neg_r' v x : Z.land v (Z.round_lor_land_bound (Z.neg x)) <= Z.land v (Z.neg x). Proof. auto with zarith. Qed.
  Lemma land_round_bound_neg_l' v x : Z.land (Z.round_lor_land_bound (Z.neg x)) v <= Z.land (Z.neg x) v. Proof. auto with zarith. Qed.
  Lemma lor_round_bound_neg_r' v x : Z.lor v (Z.round_lor_land_bound (Z.neg x)) <= Z.lor v (Z.neg x). Proof. auto with zarith. Qed.
  Lemma lor_round_bound_neg_l' v x : Z.lor (Z.round_lor_land_bound (Z.neg x)) v <= Z.lor (Z.neg x) v. Proof. auto with zarith. Qed.
  Lemma lor_round_bound_pos_r' v x : Z.lor v (Z.pos x) <= Z.lor v (Z.round_lor_land_bound (Z.pos x)). Proof. auto with zarith. Qed.
  Lemma lor_round_bound_pos_l' v x : Z.lor (Z.pos x) v <= Z.lor (Z.round_lor_land_bound (Z.pos x)) v. Proof. auto with zarith. Qed.
End Z.
