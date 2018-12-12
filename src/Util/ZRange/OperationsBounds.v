Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.CornersMonotoneBounds.
Require Import Crypto.Util.ZRange.LandLorBounds.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Morphisms.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Util.Notations.

Module ZRange.
  Local Ltac t :=
    lazymatch goal with
    | [ |- is_bounded_by_bool (?f _) (ZRange.two_corners ?f _) = true ]
      => apply (@ZRange.monotoneb_two_corners_gen f)
    | [ |- is_bounded_by_bool (?f _ _) (ZRange.four_corners ?f _ _) = true ]
      => apply (@ZRange.monotoneb_four_corners_gen f)
    | [ |- is_bounded_by_bool (?f _ _) (ZRange.four_corners_and_zero ?f _ _) = true ]
      => apply (@ZRange.monotoneb_four_corners_and_zero_gen f)
    end;
    eauto with zarith;
    repeat match goal with
           | [ |- forall x : Z, _ ] => let x := fresh "x" in intro x; destruct x
           end;
    eauto with zarith.

  Lemma is_bounded_by_bool_log2
        x x_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
  : is_bounded_by_bool (Z.log2 x) (ZRange.log2 x_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_log2_up
        x x_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
  : is_bounded_by_bool (Z.log2_up x) (ZRange.log2_up x_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_add
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.add x y) (ZRange.add x_bs y_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_sub
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.sub x y) (ZRange.sub x_bs y_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_mul
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.mul x y) (ZRange.mul x_bs y_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_div
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.div x y) (ZRange.div x_bs y_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_shiftr
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.shiftr x y) (ZRange.shiftr x_bs y_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_shiftl
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.shiftl x y) (ZRange.shiftl x_bs y_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_cc_m
        s x x_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
  : is_bounded_by_bool (Z.cc_m s x) (ZRange.cc_m s x_bs) = true.
  Proof. t. Qed.

  Lemma is_bounded_by_bool_land
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.land x y) (ZRange.land x_bs y_bs) = true.
  Proof. now apply ZRange.is_bounded_by_bool_land_bounds. Qed.

  Lemma is_bounded_by_bool_lor
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs = true)
        (Hboundedy : is_bounded_by_bool y y_bs = true)
  : is_bounded_by_bool (Z.lor x y) (ZRange.lor x_bs y_bs) = true.
  Proof. now apply ZRange.is_bounded_by_bool_lor_bounds. Qed.
End ZRange.
