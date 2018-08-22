Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Pow2.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.Lnot.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Local Ltac saturate :=
    repeat first [ progress cbv [Z.round_lor_land_bound Proper respectful Basics.flip] in *
                 | progress cbn in *
                 | progress intros
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
                   | [ H : Z.le ?x ?y |- context[2^Z.log2_up ?x] ]
                     => unique assert (2^Z.log2_up x <= 2^Z.log2_up y) by (Z.peel_le; lia)
                   end ].
  Local Ltac do_rewrites_step :=
    match goal with
    | [ |- ?R ?x ?x ] => reflexivity
    | [ |- context[Z.land (-2^_) (-2^_)] ]
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
      => rewrite (@Z.opp_mod_mod_push x y) by Z.NoZMod
    | [ H : ?x <= ?x |- _ ] => clear H
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
         | rewrite H ]
    | _ => progress autorewrite with zsimplify_const
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
    saturate; do_rewrites; fin_t.

  Local Instance land_round_Proper_pos_r x
    : Proper (Pos.le ==> Z.le)
             (fun y =>
                Z.land (Z.round_lor_land_bound x) (Z.round_lor_land_bound (Z.pos y))).
  Proof. destruct x; t. Qed.

  Local Instance land_round_Proper_pos_l y
    : Proper (Pos.le ==> Z.le)
             (fun x =>
                Z.land (Z.round_lor_land_bound (Z.pos x)) (Z.round_lor_land_bound y)).
  Proof. destruct y; t. Qed.

  Local Instance lor_round_Proper_pos_r x
    : Proper (Pos.le ==> Z.le)
             (fun y =>
                Z.lor (Z.round_lor_land_bound x) (Z.round_lor_land_bound (Z.pos y))).
  Proof. destruct x; t. Qed.

  Local Instance lor_round_Proper_pos_l y
    : Proper (Pos.le ==> Z.le)
             (fun x =>
                Z.lor (Z.round_lor_land_bound (Z.pos x)) (Z.round_lor_land_bound y)).
  Proof. destruct y; t. Qed.

  Local Instance land_round_Proper_neg_r x
    : Proper (Basics.flip Pos.le ==> Z.le)
             (fun y =>
                Z.land (Z.round_lor_land_bound x) (Z.round_lor_land_bound (Z.neg y))).
  Proof. destruct x; t. Qed.

  Local Instance land_round_Proper_neg_l y
    : Proper (Basics.flip Pos.le ==> Z.le)
             (fun x =>
                Z.land (Z.round_lor_land_bound (Z.neg x)) (Z.round_lor_land_bound y)).
  Proof. destruct y; t. Qed.

  Local Instance lor_round_Proper_neg_r x
    : Proper (Basics.flip Pos.le ==> Z.le)
             (fun y =>
                Z.lor (Z.round_lor_land_bound x) (Z.round_lor_land_bound (Z.neg y))).
  Proof. destruct x; t. Qed.

  Local Instance lor_round_Proper_neg_l y
    : Proper (Basics.flip Pos.le ==> Z.le)
             (fun x =>
                Z.lor (Z.round_lor_land_bound (Z.neg x)) (Z.round_lor_land_bound y)).
  Proof. destruct y; t. Qed.
End Z.
