Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Stabilization.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
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
  Local Coercion is_true : bool >-> Sortclass.

  (*Definition extremes_at_boundaries
             (f : Z -> Z)
             x_bs
    : forall x, is_bounded_by_bool x x_bs -> is_bounded_by_bool*)

  Lemma monotone_apply_to_range_genbP
        (P : Z -> Prop)
        (f : Z -> zrange)
        (R := fun b : bool => fun x y => P x /\ P y /\ if b then Z.le x y else Basics.flip Z.le x y)
        (Hmonotonel : exists b, Proper (R b ==> Z.le) (fun v => lower (f v)))
        (Hmonotoneu : exists b, Proper (R b ==> Z.le) (fun v => upper (f v)))
        x_bs x
        (Hboundedx : is_bounded_by_bool x x_bs)
        (x_bs_ok : forall xv, is_bounded_by_bool xv x_bs -> P xv)
    : is_tighter_than_bool (f x) (apply_to_range f x_bs).
  Proof.
    destruct x_bs as [lx ux]; simpl in *.
    cbv [is_bounded_by_bool is_true is_tighter_than_bool] in *.
    cbn [lower upper] in *.
    rewrite !Bool.andb_true_iff, !Z.leb_le_iff in *.
    setoid_rewrite Bool.andb_true_iff in x_bs_ok.
    repeat setoid_rewrite Z.leb_le_iff in x_bs_ok.
    destruct_head'_ex.
    repeat match goal with
           | [ H : Proper (R ?b ==> _) _ |- _ ]
             => unique assert (R b (if b then lx else x) (if b then x else lx)
                              /\ R b (if b then x else ux) (if b then ux else x))
               by (unfold R, Basics.flip; destruct b; repeat apply conj; eauto with omega)
           end.
    destruct_head' and.
    repeat match goal with
           | [ H : Proper (R ?b ==> _) _, H' : R ?b _ _ |- _ ]
             => unique pose proof (H _ _ H')
           end.
    destruct_head bool; split_andb; Z.ltb_to_lt; split_min_max; omega.
  Qed.

  Lemma monotone_apply_to_range_genb
        (f : Z -> zrange)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotonel : exists b, Proper (R b ==> Z.le) (fun v => lower (f v)))
        (Hmonotoneu : exists b, Proper (R b ==> Z.le) (fun v => upper (f v)))
        x_bs x
        (Hboundedx : is_bounded_by_bool x x_bs)
    : is_tighter_than_bool (f x) (apply_to_range f x_bs).
  Proof.
    apply (monotone_apply_to_range_genbP (fun _ => True)); cbv [Proper respectful] in *; eauto;
      destruct_head'_ex;
      match goal with
      | [ b : bool |- _ ] => exists b; destruct b; solve [ intuition eauto ]
      end.
  Qed.

  Lemma monotone_two_corners_genb'
        (f : Z -> Z)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotone : exists b, Proper (R b ==> Z.le) f)
        x_bs x
        (Hboundedx : is_bounded_by_bool x x_bs)
    : is_tighter_than_bool (constant (f x)) (two_corners f x_bs).
  Proof.
    cbv [two_corners].
    lazymatch goal with
    | [ |- context[apply_to_range ?f ?x_bs] ]
      => apply (monotone_apply_to_range_genb f); auto
    end.
  Qed.

  Lemma monotone_two_corners_genb
        (f : Z -> Z)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotone : exists b, Proper (R b ==> Z.le) f)
        x_bs x
        (Hboundedx : ZRange.is_bounded_by' None x_bs x)
    : ZRange.is_bounded_by' None (two_corners f x_bs) (f x).
  Proof.
    pose proof (monotone_two_corners_genb' f Hmonotone x_bs x) as H.
    cbv [constant is_bounded_by' is_bounded_by_bool is_true is_tighter_than_bool] in *.
    cbn [upper lower] in *.
    rewrite ?Bool.andb_true_iff, ?Z.leb_le_iff in *.
    tauto.
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

  (*
  Lemma monotone_four_corners_genb'
        (f : Z -> Z -> Z)
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
        (Hmonotone1 : forall x, exists b, Proper (R b ==> Z.le) (f x))
        (Hmonotone2 : forall y, exists b, Proper (R b ==> Z.le) (fun x => f x y))
        x_bs y_bs x y
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
    : is_tighter_than_bool (constant (f x y)) (four_corners f x_bs y_bs).
  Proof.
    cbv [four_corners].
    etransitivity;
      [ apply monotone_two_corners_genb'; solve [ eauto ]
      | ].
    cbv [apply_to_range union two_corners constant is_bounded_by_bool is_tighter_than_bool]; cbn [lower upper] in *.
      | lazymatch goal with
        | [ |- context[apply_to_range ?f ?x_bs] ]
          => apply (monotone_apply_to_range_genb f); [ | | eassumption ]
        end ];
      auto.
    { cbv [two_corners constant apply_to_range union flip].
      cbn [lower upper].
      subst R.
      cbv [is_bounded_by_bool is_true] in *; split_andb; Z.ltb_to_lt.
      assert (Hx_good : lower x_bs <= upper x_bs) by omega.
      assert (Hy_good : lower y_bs <= upper y_bs) by omega.
      pose proof (Hmonotone2 (lower y_bs)).
      pose proof (Hmonotone2 (upper y_bs)).
      destruct_head'_ex; destruct_head'_bool; [ exists true | | | exists false ];
        try intros ?? Hc;
        repeat match goal with
               | [ H : Proper _ _ |- _ ] => specialize (H _ _ Hc)
               end;
        split_min_max; cbn beta in *; try omega.
      all: pose proof (Hmonotone1 (lower x_bs)).
      all: pose proof (Hmonotone1 (upper x_bs)).
      all: destruct_head'_ex.
      all: destruct_head'_bool.
      all: repeat match goal with
                  | [ H : Proper _ (fun x => ?f x _) |- _ ]
                    => unique pose proof (H _ _ Hx_good)
                  | [ H : Proper _ (?f _) |- _ ]
                    => unique pose proof (H _ _ Hy_good)
                  end;
        cbn beta in *.
      cbv [Basics.flip] in *.
      all:try omega.

      repeat match goal with
             | [
      { exists true.

    cbv [two_corners].

  Qed.*)

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
    destruct_head bool.
    all: revert_min_max; intros.
    all: (split; [ repeat (etransitivity; [ | eassumption ]) | repeat (etransitivity; [ eassumption | ]) ]).
    all: auto using Z.le_min_l, Z.le_min_r, Z.le_max_l, Z.le_max_r.
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
    destruct_head bool.
    all: revert_min_max; intros.
    all: (split; [ repeat (etransitivity; [ | eassumption ]) | repeat (etransitivity; [ eassumption | ]) ]).
    all: auto using Z.le_min_l, Z.le_min_r, Z.le_max_l, Z.le_max_r.
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
