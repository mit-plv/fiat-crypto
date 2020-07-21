Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.LandLorBounds.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.Morphisms.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.CornersMonotoneBounds.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Module ZRange.
  Import Operations.ZRange.
  Import CornersMonotoneBounds.ZRange.

  Lemma is_bounded_by_bool_lor_land_bound_helper
        f (Hf : f = Z.lor \/ f = Z.land)
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
    : is_tighter_than_bool
        (constant (f (Z.round_lor_land_bound x) (Z.round_lor_land_bound y)))
        (four_corners_and_zero (fun x y => f (Z.round_lor_land_bound x) (Z.round_lor_land_bound y)) x_bs y_bs)
      = true.
  Proof.
    apply monotoneb_four_corners_and_zero_gen with (x:=x) (y:=y);
      destruct_head'_or; subst f; eauto with typeclass_instances zarith core.
  Qed.

  Local Existing Instances Z.land_round_Proper_pos_r
        Z.land_round_Proper_pos_l
        Z.lor_round_Proper_pos_r
        Z.lor_round_Proper_pos_l
        Z.land_round_Proper_neg_r
        Z.land_round_Proper_neg_l
        Z.lor_round_Proper_neg_r
        Z.lor_round_Proper_neg_l.

  Lemma is_bounded_by_bool_land_lor_bounds_helper
        f (Hf : f = Z.lor \/ f = Z.land)
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
    : is_bounded_by_bool (f x y) (land_lor_bounds f x_bs y_bs) = true.
  Proof.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf x (extend_land_lor_bounds x_bs) y (extend_land_lor_bounds y_bs)) as H.
    pose proof (fun pf1 pf2 => is_bounded_by_bool_lor_land_bound_helper f Hf 0 (extend_land_lor_bounds x_bs) y (extend_land_lor_bounds y_bs) pf2 pf1) as H0x.
    pose proof (fun pf1 pf2 => is_bounded_by_bool_lor_land_bound_helper f Hf (-1) (extend_land_lor_bounds x_bs) y (extend_land_lor_bounds y_bs) pf2 pf1) as Hm1x.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf x (extend_land_lor_bounds x_bs) 0 (extend_land_lor_bounds y_bs)) as H0y.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf x (extend_land_lor_bounds x_bs) (-1) (extend_land_lor_bounds y_bs)) as Hm1y.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf 0 (extend_land_lor_bounds x_bs) 0 (extend_land_lor_bounds y_bs)) as H00.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf (-1) (extend_land_lor_bounds x_bs) 0 (extend_land_lor_bounds y_bs)) as Hm10.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf 0 (extend_land_lor_bounds x_bs) (-1) (extend_land_lor_bounds y_bs)) as H0m1.
    pose proof (is_bounded_by_bool_lor_land_bound_helper f Hf (-1) (extend_land_lor_bounds x_bs) (-1) (extend_land_lor_bounds y_bs)) as Hm1m1.
    specialize_by (eapply ZRange.is_bounded_by_of_is_tighter_than; try eapply ZRange.is_tighter_than_bool_extend_land_lor_bounds; eassumption || reflexivity).
    revert H H0x Hm1x H0y Hm1y H00 Hm1m1 H0m1 Hm10.
    cbv [land_lor_bounds constant is_tighter_than_bool is_bounded_by_bool is_true] in *; cbn [lower upper] in *.
    rewrite !Bool.andb_true_iff, !Z.leb_le in *.
    cbv [extend_land_lor_bounds].
    cbn [lower upper] in *.
    destruct (Z.round_lor_land_bound_bounds x) as [Hx|Hx], (Z.round_lor_land_bound_bounds y) as [Hy|Hy].
    all: repeat apply Z.min_case_strong; repeat apply Z.max_case_strong.
    all: try (intros; exfalso; clear dependent f; lia).
    all: destruct x as [|x|x], y as [|y|y]; try (intros; exfalso; clear dependent f; lia).
    all: change (Z.round_lor_land_bound 0) with 0 in *.
    all: change (Z.round_lor_land_bound (-1)) with (-1) in *.
    all: intros.
    all: repeat match goal with
                | _ => assumption
                | [ H : ?T, H' : ?T |- _ ] => clear H'
                | [ H : 0 <= 0 <= 0 |- _ ] => clear H
                | [ H : 0 <= -1 <= _ -> _ |- _ ] => clear H
                | [ H : 0 <= -1 -> _ |- _ ] => clear H
                | [ H : ?x <= ?x <= _ -> _ |- _ ] => specialize (fun pf => H (conj (@Z.le_refl x) pf))
                | [ H : _ <= ?x <= ?x -> _ |- _ ] => specialize (fun pf => H (conj pf (@Z.le_refl x)))
                | [ H : ?T, H' : ?T /\ _ -> _ |- _ ] => specialize (fun pf => H' (conj H pf))
                | [ H : ?T, H' : _ /\ ?T -> _ |- _ ] => specialize (fun pf => H' (conj pf H))
                | _ => progress specialize_by_assumption
                | _ => progress specialize_by (destruct_head'_and; assumption)
                | [ H : _ <= Z.pos _ <= ?x |- _ ] => unique assert (0 <= x) by (clear -H; lia)
                | [ H : ?x <= Z.neg _ <= _ |- _ ] => unique assert (x <= -1) by (clear -H; lia)
                | [ H : ?a <= _ <= ?c, H' : ?c <= ?d, H'' : ?a <= ?d -> _ |- _ ]
                  => unique assert (a <= d) by (clear -H H'; lia)
                | [ H : ?a <= ?b -> ?c <= ?d <= ?e -> _ |- _ ] => specialize (fun pf1 pf2 => H pf2 pf1)
                end.
    all: destruct Hf; subst f.
    all: split.
    all: destruct_head'_and.
    all: split_and.
    all: repeat lazymatch goal with
                | [ |- Z.land _ (Z.pos ?x) <= _ ]
                  => is_var x; etransitivity; [ apply Z.land_round_bound_pos_r' | ]
                | [ |- Z.land (Z.pos ?x) _ <= _ ]
                  => is_var x; etransitivity; [ apply Z.land_round_bound_pos_l' | ]
                | [ |- _ <= Z.land _ (Z.pos ?x) ]
                  => is_var x; etransitivity; [ | apply Z.land_round_bound_pos_r ]
                | [ |- _ <= Z.land (Z.pos ?x) _ ]
                  => is_var x; etransitivity; [ | apply Z.land_round_bound_pos_l ]
                | [ |- Z.land _ (Z.neg ?x) <= _ ]
                  => is_var x; etransitivity; [ apply Z.land_round_bound_neg_r | ]
                | [ |- Z.land (Z.neg ?x) _ <= _ ]
                  => is_var x; etransitivity; [ apply Z.land_round_bound_neg_l | ]
                | [ |- _ <= Z.land _ (Z.neg ?x) ]
                  => is_var x; etransitivity; [ | apply Z.land_round_bound_neg_r' ]
                | [ |- _ <= Z.land (Z.neg ?x) _ ]
                  => is_var x; etransitivity; [ | apply Z.land_round_bound_neg_l' ]
                | [ |- Z.lor _ (Z.pos ?x) <= _ ]
                  => is_var x; etransitivity; [ apply Z.lor_round_bound_pos_r' | ]
                | [ |- Z.lor (Z.pos ?x) _ <= _ ]
                  => is_var x; etransitivity; [ apply Z.lor_round_bound_pos_l' | ]
                | [ |- _ <= Z.lor _ (Z.pos ?x) ]
                  => is_var x; etransitivity; [ | apply Z.lor_round_bound_pos_r ]
                | [ |- _ <= Z.lor (Z.pos ?x) _ ]
                  => is_var x; etransitivity; [ | apply Z.lor_round_bound_pos_l ]
                | [ |- Z.lor _ (Z.neg ?x) <= _ ]
                  => is_var x; etransitivity; [ apply Z.lor_round_bound_neg_r | ]
                | [ |- Z.lor (Z.neg ?x) _ <= _ ]
                  => is_var x; etransitivity; [ apply Z.lor_round_bound_neg_l | ]
                | [ |- _ <= Z.lor _ (Z.neg ?x) ]
                  => is_var x; etransitivity; [ | apply Z.lor_round_bound_neg_r' ]
                | [ |- _ <= Z.lor (Z.neg ?x) _ ]
                  => is_var x; etransitivity; [ | apply Z.lor_round_bound_neg_l' ]
                | [ |- Z.pos ?x <= _ ]
                  => is_var x; etransitivity; [ eassumption | ]
                | [ |- _ <= Z.neg ?x ]
                  => is_var x; etransitivity; [ | eassumption ]
                | [ |- _ <= Z.pos ?x ]
                  => is_var x; transitivity 0; [ assumption | lia ]
                | [ |- Z.neg ?x <= _ ]
                  => is_var x; transitivity (-1); [ lia | assumption ]
                | _ => idtac
                end.
    all: try assumption.
    all: try (rewrite ?Z.lor_0_l, ?Z.lor_0_r, ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_m1_l, ?Z.lor_m1_r, ?Z.land_m1_l, ?Z.land_m1_r in *; reflexivity || assumption).
  Qed.

  Lemma is_bounded_by_bool_land_bounds
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
    : is_bounded_by_bool (Z.land x y) (ZRange.land_bounds x_bs y_bs) = true.
  Proof.
    cbv [ZRange.land_bounds].
    cbv [is_bounded_by_bool] in *.
    cbn [upper lower].
    repeat match goal with
           | H : (_ && _)%bool = true |- _ =>
             apply Bool.andb_true_iff in H; destruct H
           end.
    Z.ltb_to_lt.
    pose proof (Z.log2_up_le_mono (-x) (- lower x_bs) ltac:(lia)).
    pose proof (Z.log2_up_le_mono (-y) (- lower y_bs) ltac:(lia)).
    assert (0 <= 2 ^ (Z.max (Z.log2_up (- lower x_bs))
                            (Z.log2_up (- lower y_bs))))
      by (apply Z.pow_nonneg; lia).
    pose proof (Z.pow_le_mono
                  2 (Z.max (Z.log2_up (- x)) (Z.log2_up (- y)))
                  2 (Z.max (Z.log2_up (- lower x_bs)) (Z.log2_up (- lower y_bs)))
                  ltac:(lia) ltac:(lia)).
    destruct (Z_lt_le_dec x 0); destruct (Z_lt_le_dec y 0).
    all:lazymatch goal with
        | Hx : ?x < 0, Hy : ?y < 0 |- context [Z.land ?x ?y] =>
          pose proof (Z.land_neg_lower x y ltac:(lia) ltac:(lia));
            pose proof (proj2 (Z.land_neg x y) ltac:(lia));
            pose proof (Z.land_le x y ltac:(lia))
        | Hx : ?x < 0, Hy : 0 <= ?y |- context [Z.land ?x ?y] =>
          pose proof (Z.land_neg_l_range x y ltac:(lia) ltac:(lia));
            pose proof (proj2 (Z.land_nonneg x y) ltac:(lia))
        | Hx : 0 <= ?x, Hy : ?y < 0 |- context [Z.land ?x ?y] =>
          pose proof (Z.land_neg_r_range x y ltac:(lia) ltac:(lia));
            pose proof (proj2 (Z.land_nonneg x y) ltac:(lia))
        | Hx : 0 <= ?x, Hy : 0 <= ?y |- context [Z.land ?x ?y] =>
          pose proof (Z.land_le x y ltac:(lia));
            let H := fresh in
            pose proof (Z.land_le y x ltac:(lia)) as H;
              rewrite Z.land_comm in H;
              pose proof (proj2 (Z.land_nonneg x y) ltac:(lia))
        end.
    all:break_innermost_match;
      repeat match goal with
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H; destruct H
             | H : (_ && _)%bool = false |- _ =>
               apply Bool.andb_false_iff in H; destruct H
             end; Z.ltb_to_lt.
    all:try lia.
    all:apply Bool.andb_true_iff; split;
      Z.ltb_to_lt; try lia.
  Qed.

  Lemma is_bounded_by_bool_lor_bounds
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
    : is_bounded_by_bool (Z.lor x y) (ZRange.lor_bounds x_bs y_bs) = true.
  Proof. apply is_bounded_by_bool_land_lor_bounds_helper; auto. Qed.
End ZRange.
