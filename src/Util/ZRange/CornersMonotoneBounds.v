Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Stabilization.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope Z_scope.

Module ZRange.
  Import Operations.ZRange.
  Local Arguments is_bounded_by' !_ _ _ / .

  Lemma monotone_two_corners_genb
        (f : Z -> Z)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotone : exists b, Proper (R b ==> Z.le) f)
        x_bs x
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
    : ZRange.is_bounded_by' None (two_corners f x_bs) (f x).
  Proof.
    split; trivial.
    destruct x_bs as [lx ux]; simpl in *.
    destruct Hboundedx as [Hboundedx _].
    destruct_head'_ex.
    repeat match goal with
           | [ H : Proper (R ?b ==> Z.le) f |- _ ]
             => unique assert (R b (if b then lx else x) (if b then x else lx)
                               /\ R b (if b then x else ux) (if b then ux else x))
               by (unfold R, Basics.flip; destruct b; omega)
           end.
    destruct_head' and.
    repeat match goal with
           | [ H : Proper (R ?b ==> Z.le) _, H' : R ?b _ _ |- _ ]
             => unique pose proof (H _ _ H')
           end.
    destruct_head bool; split_min_max; omega.
  Qed.

  Lemma monotone_two_corners_gen
        (f : Z -> Z)
        (Hmonotone : Proper (Z.le ==> Z.le) f \/ Proper (Basics.flip Z.le ==> Z.le) f)
        x_bs x
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
    : ZRange.is_bounded_by' None (ZRange.two_corners f x_bs) (f x).
  Proof.
    eapply monotone_two_corners_genb; auto.
    destruct Hmonotone; [ exists true | exists false ]; assumption.
  Qed.
  Lemma monotone_two_corners
        (b : bool)
        (f : Z -> Z)
        (R := if b then Z.le else Basics.flip Z.le)
        (Hmonotone : Proper (R ==> Z.le) f)
        x_bs x
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
    : ZRange.is_bounded_by' None (ZRange.two_corners f x_bs) (f x).
  Proof.
    apply monotone_two_corners_genb; auto; subst R;
      exists b.
    intros ???; apply Hmonotone; auto.
  Qed.

  Lemma monotone_four_corners_genb
        (f : Z -> Z -> Z)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotone1 : forall x, exists b, Proper (R b ==> Z.le) (f x))
        (Hmonotone2 : forall y, exists b, Proper (R b ==> Z.le) (fun x => f x y))
        x_bs y_bs x y
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
        (Hboundedy : ZRange.is_bounded_by' None y_bs y)
    : ZRange.is_bounded_by' None (ZRange.four_corners f x_bs y_bs) (f x y).
  Proof.
    destruct x_bs as [lx ux].
    cbn [ZRange.four_corners lower upper].
    pose proof (monotone_two_corners_genb (f lx) (Hmonotone1 _) _ _ Hboundedy) as Hmono_fl.
    pose proof (monotone_two_corners_genb (f ux) (Hmonotone1 _) _ _ Hboundedy) as Hmono_fu.
    repeat match goal with
           | [ |- context[ZRange.two_corners ?x ?y] ]
             => let l := fresh "lf" in
                let u := fresh "uf" in
                generalize dependent (ZRange.two_corners x y); intros [l u]; intros
           end.
    unfold ZRange.is_bounded_by', union in *; simpl in *; split; trivial.
    destruct_head'_and; destruct_head' True.
    pose proof (Hmonotone2 y).
    destruct_head'_ex.
    repeat match goal with
           | [ H : Proper (R ?b ==> Z.le) (f _) |- _ ]
             => unique assert (R b (if b then ly else y) (if b then y else ly)
                               /\ R b (if b then y else uy) (if b then uy else y))
               by (unfold R, Basics.flip; destruct b; omega)
           | [ H : Proper (R ?b ==> Z.le) (fun x => f x _) |- _ ]
             => unique assert (R b (if b then lx else x) (if b then x else lx)
                               /\ R b (if b then x else ux) (if b then ux else x))
               by (unfold R, Basics.flip; destruct b; omega)
           end.
    destruct_head' and.
    repeat match goal with
           | [ H : Proper (R ?b ==> Z.le) _, H' : R ?b _ _ |- _ ]
             => unique pose proof (H _ _ H')
           end; cbv beta in *.
    destruct_head bool; split_min_max; omega.
  Qed.

  Lemma monotone_four_corners_gen
        (f : Z -> Z -> Z)
        (Hmonotone1 : forall x, Proper (Z.le ==> Z.le) (f x) \/ Proper (Basics.flip Z.le ==> Z.le) (f x))
        (Hmonotone2 : forall y, Proper (Z.le ==> Z.le) (fun x => f x y) \/ Proper (Basics.flip Z.le ==> Z.le) (fun x => f x y))
        x_bs y_bs x y
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
        (Hboundedy : ZRange.is_bounded_by' None y_bs y)
    : ZRange.is_bounded_by' None (ZRange.four_corners f x_bs y_bs) (f x y).
  Proof.
    eapply monotone_four_corners_genb; auto.
    { intro x'; destruct (Hmonotone1 x'); [ exists true | exists false ]; assumption. }
    { intro x'; destruct (Hmonotone2 x'); [ exists true | exists false ]; assumption. }
  Qed.
  Lemma monotone_four_corners
        (b1 b2 : bool)
        (f : Z -> Z -> Z)
        (R1 := if b1 then Z.le else Basics.flip Z.le) (R2 := if b2 then Z.le else Basics.flip Z.le)
        (Hmonotone : Proper (R1 ==> R2 ==> Z.le) f)
        x_bs y_bs x y
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
        (Hboundedy : ZRange.is_bounded_by' None y_bs y)
    : ZRange.is_bounded_by' None (ZRange.four_corners f x_bs y_bs) (f x y).
  Proof.
    apply monotone_four_corners_genb; auto; intro x'; subst R1 R2;
      [ exists b2 | exists b1 ];
      [ eapply (Hmonotone x' x'); destruct b1; reflexivity
      | intros ???; apply Hmonotone; auto; destruct b2; reflexivity ].
  Qed.

  Lemma monotone_eight_corners_genb
        (f : Z -> Z -> Z -> Z)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotone1 : forall x y, exists b, Proper (R b ==> Z.le) (f x y))
        (Hmonotone2 : forall x z, exists b, Proper (R b ==> Z.le) (fun y => f x y z))
        (Hmonotone3 : forall y z, exists b, Proper (R b ==> Z.le) (fun x => f x y z))
        x_bs y_bs z_bs x y z
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
        (Hboundedy : ZRange.is_bounded_by' None y_bs y)
        (Hboundedz : ZRange.is_bounded_by' None z_bs z)
    : ZRange.is_bounded_by' None (ZRange.eight_corners f x_bs y_bs z_bs) (f x y z).
  Proof.
    destruct x_bs as [lx ux].
    unfold ZRange.eight_corners; cbn [lower upper].
    pose proof (monotone_four_corners_genb (f lx) (Hmonotone1 _) (Hmonotone2 _) _ _ _ _ Hboundedy Hboundedz) as Hmono_fl.
    pose proof (monotone_four_corners_genb (f ux) (Hmonotone1 _) (Hmonotone2 _) _ _ _ _ Hboundedy Hboundedz) as Hmono_fu.
    repeat match goal with
           | [ |- context[ZRange.four_corners ?x ?y ?z] ]
             => let l := fresh "lf" in
                let u := fresh "uf" in
                generalize dependent (ZRange.four_corners x y z); intros [l u]; intros
           end.
    unfold ZRange.is_bounded_by' in *; simpl in *; split; trivial.
    destruct_head'_and; destruct_head' True.
    pose proof (Hmonotone3 y z).
    destruct_head'_ex.
    repeat match goal with
           | [ H : Proper (R ?b ==> Z.le) (f _ _) |- _ ]
             => unique assert (R b (if b then lz else z) (if b then z else lz)
                               /\ R b (if b then z else uz) (if b then uz else z))
               by (unfold R, Basics.flip; destruct b; omega)
           | [ H : Proper (R ?b ==> Z.le) (fun y' => f _ y' _) |- _ ]
             => unique assert (R b (if b then ly else y) (if b then y else ly)
                               /\ R b (if b then y else uy) (if b then uy else y))
               by (unfold R, Basics.flip; destruct b; omega)
           | [ H : Proper (R ?b ==> Z.le) (fun x' => f x' _ _) |- _ ]
             => unique assert (R b (if b then lx else x) (if b then x else lx)
                               /\ R b (if b then x else ux) (if b then ux else x))
               by (unfold R, Basics.flip; destruct b; omega)
           end.
    destruct_head' and.
    repeat match goal with
           | [ H : Proper (R ?b ==> Z.le) _, H' : R ?b _ _ |- _ ]
             => unique pose proof (H _ _ H')
           end.
    destruct_head bool; split_min_max; omega.
  Qed.

  Lemma monotone_eight_corners_gen
        (f : Z -> Z -> Z -> Z)
        (Hmonotone1 : forall x y, Proper (Z.le ==> Z.le) (f x y) \/ Proper (Basics.flip Z.le ==> Z.le) (f x y))
        (Hmonotone2 : forall x z, Proper (Z.le ==> Z.le) (fun y => f x y z) \/ Proper (Basics.flip Z.le ==> Z.le) (fun y => f x y z))
        (Hmonotone3 : forall y z, Proper (Z.le ==> Z.le) (fun x => f x y z) \/ Proper (Basics.flip Z.le ==> Z.le) (fun x => f x y z))
        x_bs y_bs z_bs x y z
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
        (Hboundedy : ZRange.is_bounded_by' None y_bs y)
        (Hboundedz : ZRange.is_bounded_by' None z_bs z)
    : ZRange.is_bounded_by' None (ZRange.eight_corners f x_bs y_bs z_bs) (f x y z).
  Proof.
    eapply monotone_eight_corners_genb; auto.
    { intros x' y'; destruct (Hmonotone1 x' y'); [ exists true | exists false ]; assumption. }
    { intros x' y'; destruct (Hmonotone2 x' y'); [ exists true | exists false ]; assumption. }
    { intros x' y'; destruct (Hmonotone3 x' y'); [ exists true | exists false ]; assumption. }
  Qed.
  Lemma monotone_eight_corners
        (b1 b2 b3 : bool)
        (f : Z -> Z -> Z -> Z)
        (R1 := if b1 then Z.le else Basics.flip Z.le)
        (R2 := if b2 then Z.le else Basics.flip Z.le)
        (R3 := if b3 then Z.le else Basics.flip Z.le)
        (Hmonotone : Proper (R1 ==> R2 ==> R3 ==> Z.le) f)
        x_bs y_bs z_bs x y z
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
        (Hboundedy : ZRange.is_bounded_by' None y_bs y)
        (Hboundedz : ZRange.is_bounded_by' None z_bs z)
    : ZRange.is_bounded_by' None (ZRange.eight_corners f x_bs y_bs z_bs) (f x y z).
  Proof.
    apply monotone_eight_corners_genb; auto; intro x'; subst R1 R2 R3;
      [ exists b3 | exists b2 | exists b1 ];
      intros ???; apply Hmonotone; break_innermost_match; try reflexivity; trivial.
  Qed.

  Lemma monotonify2 (f : Z -> Z -> Z) (upper : Z -> Z -> Z)
        (Hbounded : forall a b, Z.abs (f a b) <= upper (Z.abs a) (Z.abs b))
        (Hupper_monotone : Proper (Z.le ==> Z.le ==> Z.le) upper)
        {xb yb x y}
        (Hboundedx : ZRange.is_bounded_by' None xb x)
        (Hboundedy : ZRange.is_bounded_by' None yb y)
        (abs_x := ZRange.upper (ZRange.abs xb))
        (abs_y := ZRange.upper (ZRange.abs yb))
    : ZRange.is_bounded_by'
        None
        {| ZRange.lower := -upper abs_x abs_y;
           ZRange.upper := upper abs_x abs_y |}
        (f x y).
  Proof.
    split; [ | exact I ]; subst abs_x abs_y; simpl.
    apply Z.abs_le.
    destruct Hboundedx as [Hx _], Hboundedy as [Hy _].
    etransitivity; [ apply Hbounded | ].
    apply Hupper_monotone;
      unfold ZRange.abs;
      repeat (apply Z.max_case_strong || apply Zabs_ind); omega.
  Qed.
End ZRange.
