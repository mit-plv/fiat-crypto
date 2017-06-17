Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.Tactics.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Stabilization.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope Z_scope.

Local Arguments Bounds.is_bounded_by' !_ _ _ / .

Lemma is_bounded_by_truncation_bounds Tout bs v
      (H : Bounds.is_bounded_by (T:=Tbase TZ) bs v)
  : Bounds.is_bounded_by (T:=Tbase Tout)
                         (Bounds.truncation_bounds (Bounds.bit_width_of_base_type Tout) bs)
                         (ZToInterp v).
Proof.
  destruct bs as [l u]; cbv [Bounds.truncation_bounds Bounds.is_bounded_by Bounds.is_bounded_by' Bounds.bit_width_of_base_type Bounds.log_bit_width_of_base_type option_map ZRange.is_bounded_by'] in *; simpl in *.
  repeat first [ break_t_step
               | fin_t
               | progress simpl in *
               | Zarith_t_step
               | rewriter_t
               | word_arith_t ].
Qed.

Lemma is_bounded_by_compose T1 T2 f_v bs v f_bs fv
      (H : Bounds.is_bounded_by (T:=Tbase T1) bs v)
      (Hf : forall bs v, Bounds.is_bounded_by (T:=Tbase T1) bs v -> Bounds.is_bounded_by (T:=Tbase T2) (f_bs bs) (f_v v))
      (Hfv : f_v v = fv)
  : Bounds.is_bounded_by (T:=Tbase T2) (f_bs bs) fv.
Proof.
  subst; eauto.
Qed.

Lemma monotone_two_corners_genb
      (f : Z -> Z)
      (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
      (Hmonotone : exists b, Proper (R b ==> Z.le) f)
      x_bs x
      (Hboundedx : ZRange.is_bounded_by' None x_bs x)
  : ZRange.is_bounded_by' None (Bounds.two_corners f x_bs) (f x).
Proof.
  unfold ZRange.is_bounded_by' in *; split; trivial.
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
  : ZRange.is_bounded_by' None (Bounds.two_corners f x_bs) (f x).
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
  : ZRange.is_bounded_by' None (Bounds.two_corners f x_bs) (f x).
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
  : ZRange.is_bounded_by' None (Bounds.four_corners f x_bs y_bs) (f x y).
Proof.
  destruct x_bs as [lx ux], y_bs as [ly uy].
  unfold Bounds.four_corners.
  pose proof (monotone_two_corners_genb (f lx) (Hmonotone1 _) _ _ Hboundedy) as Hmono_fl.
  pose proof (monotone_two_corners_genb (f ux) (Hmonotone1 _) _ _ Hboundedy) as Hmono_fu.
  repeat match goal with
         | [ |- context[Bounds.two_corners ?x ?y] ]
           => let l := fresh "lf" in
              let u := fresh "uf" in
              generalize dependent (Bounds.two_corners x y); intros [l u]; intros
         end.
  unfold ZRange.is_bounded_by' in *; simpl in *; split; trivial.
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
  : ZRange.is_bounded_by' None (Bounds.four_corners f x_bs y_bs) (f x y).
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
  : ZRange.is_bounded_by' None (Bounds.four_corners f x_bs y_bs) (f x y).
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
  : ZRange.is_bounded_by' None (Bounds.eight_corners f x_bs y_bs z_bs) (f x y z).
Proof.
  destruct x_bs as [lx ux], y_bs as [ly uy], z_bs as [lz uz].
  unfold Bounds.eight_corners.
  pose proof (monotone_four_corners_genb (f lx) (Hmonotone1 _) (Hmonotone2 _) _ _ _ _ Hboundedy Hboundedz) as Hmono_fl.
  pose proof (monotone_four_corners_genb (f ux) (Hmonotone1 _) (Hmonotone2 _) _ _ _ _ Hboundedy Hboundedz) as Hmono_fu.
  repeat match goal with
         | [ |- context[Bounds.four_corners ?x ?y ?z] ]
           => let l := fresh "lf" in
              let u := fresh "uf" in
              generalize dependent (Bounds.four_corners x y z); intros [l u]; intros
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
  : ZRange.is_bounded_by' None (Bounds.eight_corners f x_bs y_bs z_bs) (f x y z).
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
  : ZRange.is_bounded_by' None (Bounds.eight_corners f x_bs y_bs z_bs) (f x y z).
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
  : ZRange.is_bounded_by'
      None
      {| ZRange.lower := -upper (Bounds.max_abs_bound xb) (Bounds.max_abs_bound yb);
         ZRange.upper := upper (Bounds.max_abs_bound xb) (Bounds.max_abs_bound yb) |}
      (f x y).
Proof.
  split; [ | exact I ]; simpl.
  apply Z.abs_le.
  destruct Hboundedx as [Hx _], Hboundedy as [Hy _].
  etransitivity; [ apply Hbounded | ].
  apply Hupper_monotone;
    unfold Bounds.max_abs_bound;
    repeat (apply Z.max_case_strong || apply Zabs_ind); omega.
Qed.

Local Existing Instances Z.log2_up_le_Proper Z.add_le_Proper Z.sub_with_borrow_le_Proper.
Lemma land_upper_lor_land_bounds a b
  : Z.abs (Z.land a b) <= Bounds.upper_lor_and_bounds (Z.abs a) (Z.abs b).
Proof.
  unfold Bounds.upper_lor_and_bounds.
  apply stabilizes_bounded; auto with zarith.
  rewrite <- !Z.max_mono by exact _.
  apply land_stabilizes; apply stabilization_time_weaker.
Qed.

Lemma lor_upper_lor_land_bounds a b
  : Z.abs (Z.lor a b) <= Bounds.upper_lor_and_bounds (Z.abs a) (Z.abs b).
Proof.
  unfold Bounds.upper_lor_and_bounds.
  apply stabilizes_bounded; auto with zarith.
  rewrite <- !Z.max_mono by exact _.
  apply lor_stabilizes; apply stabilization_time_weaker.
Qed.

Lemma upper_lor_and_bounds_Proper
  : Proper (Z.le ==> Z.le ==> Z.le) Bounds.upper_lor_and_bounds.
Proof.
  intros ??? ???.
  unfold Bounds.upper_lor_and_bounds.
  auto with zarith.
Qed.

Local Arguments Z.pow !_ !_.
Local Arguments Z.log2_up !_.
Local Arguments Z.add !_ !_.
Lemma land_bounds_extreme xb yb x y
      (Hx : ZRange.is_bounded_by' None xb x)
      (Hy : ZRange.is_bounded_by' None yb y)
  : ZRange.is_bounded_by' None (Bounds.extreme_lor_land_bounds xb yb) (Z.land x y).
Proof.
  apply monotonify2; auto;
    unfold Bounds.extreme_lor_land_bounds;
    [ apply land_upper_lor_land_bounds
    | apply upper_lor_and_bounds_Proper ].
Qed.
Lemma lor_bounds_extreme xb yb x y
      (Hx : ZRange.is_bounded_by' None xb x)
      (Hy : ZRange.is_bounded_by' None yb y)
  : ZRange.is_bounded_by' None (Bounds.extreme_lor_land_bounds xb yb) (Z.lor x y).
Proof.
  apply monotonify2; auto;
    unfold Bounds.extreme_lor_land_bounds;
    [ apply lor_upper_lor_land_bounds
    | apply upper_lor_and_bounds_Proper ].
Qed.

Local Arguments N.ldiff : simpl never.
Local Arguments Z.pow : simpl never.
Local Arguments Z.add !_ !_.
Local Existing Instances Z.add_le_Proper Z.sub_le_flip_le_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper Z.sub_le_eq_Proper Z.add_with_carry_le_Proper.
Local Hint Extern 1 => progress cbv beta iota : typeclass_instances.
Local Ltac ibbio_do_cbv :=
  cbv [Bounds.interp_op Zinterp_op Z.add_with_get_carry SmartFlatTypeMapUnInterp Bounds.add_with_get_carry Bounds.sub_with_get_borrow Bounds.get_carry Bounds.get_borrow Z.get_carry cast_const Bounds.mul_split]; cbn [fst snd].
Local Ltac ibbio_prefin_by_apply :=
  [ > | intros; apply is_bounded_by_truncation_bounds | simpl; reflexivity ].
Local Ltac handle_mul :=
  apply monotone_four_corners_genb; try (split; auto);
  unfold Basics.flip;
  let x := fresh "x" in
  intro x;
  exists (0 <=? x);
  break_match; Z.ltb_to_lt;
  intros ???; nia.
Lemma is_bounded_by_interp_op t tR (opc : op t tR)
      (bs : interp_flat_type Bounds.interp_base_type _)
      (v : interp_flat_type interp_base_type _)
      (H : Bounds.is_bounded_by bs v)
      (H_side : to_prop (interped_op_side_conditions opc v))
  : Bounds.is_bounded_by (Bounds.interp_op opc bs) (Syntax.interp_op _ _ opc v).
Proof.
  destruct opc;
    [ apply is_bounded_by_truncation_bounds..
    | split; ibbio_do_cbv;
      [ eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v mod _)) (v:=ZToInterp _);
        [ .. | cbn -[Z.mul_split_at_bitwidth]; rewrite Z.mul_split_at_bitwidth_mod ];
        ibbio_prefin_by_apply
      | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v / _))   (v:=ZToInterp _);
        [ .. | cbn -[Z.mul_split_at_bitwidth]; rewrite Z.mul_split_at_bitwidth_div ];
        ibbio_prefin_by_apply ]
    | apply is_bounded_by_truncation_bounds
    | split; ibbio_do_cbv;
      [ eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v mod _)) (v:=ZToInterp _);
        ibbio_prefin_by_apply
      | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v / _))   (v:=ZToInterp _);
        ibbio_prefin_by_apply ]
    | apply is_bounded_by_truncation_bounds
    | split; ibbio_do_cbv;
      [ eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v mod _)) (v:=ZToInterp _);
        ibbio_prefin_by_apply
      | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (-(v / _)))   (v:=ZToInterp _);
        ibbio_prefin_by_apply ] ];
    repeat first [ progress simpl in *
                 | progress cbv [interp_op lift_op cast_const Bounds.interp_base_type Bounds.is_bounded_by' ZRange.is_bounded_by'] in *
                 | progress destruct_head'_prod
                 | progress destruct_head'_and
                 | omega
                 | match goal with
                   | [ |- context[interpToZ ?x] ]
                     => generalize dependent (interpToZ x); clear x; intros
                   | [ |- _ /\ True ] => split; [ | tauto ]
                   end ].
  { apply (@monotone_four_corners true true _ _); split; auto. }
  { apply (@monotone_four_corners true false _ _); split; auto. }
  { handle_mul. }
  { apply monotone_four_corners_genb; try (split; auto);
      [ eexists; apply Z.shiftl_le_Proper1
      | exists true; apply Z.shiftl_le_Proper2 ]. }
  { apply monotone_four_corners_genb; try (split; auto);
      [ eexists; apply Z.shiftr_le_Proper1
      | exists true; apply Z.shiftr_le_Proper2 ]. }
  { break_innermost_match;
      try (apply land_bounds_extreme; split; auto);
      repeat first [ progress simpl in *
                   | Zarith_t_step
                   | rewriter_t
                   | progress saturate_land_lor_facts
                   | split_min_max; omega ]. }
  { break_innermost_match;
      try (apply lor_bounds_extreme; split; auto);
      repeat first [ progress simpl in *
                   | Zarith_t_step
                   | rewriter_t
                   | progress Zarith_land_lor_t_step
                   | solve [ split_min_max; try omega; try Zarith_land_lor_t_step ] ]. }
  { repeat first [ progress destruct_head Bounds.t
                 | progress simpl in *
                 | progress split_min_max
                 | omega ]. }
  { break_innermost_match; simpl in *; Z.ltb_to_lt; subst;
      split; assumption. }
  { destruct_head Bounds.t; cbv [Bounds.zselect' Z.zselect].
    break_innermost_match; split_min_max; omega. }
  { handle_mul. }
  { apply Z.mod_bound_min_max; auto. }
  { handle_mul. }
  { auto with zarith. }
  { apply (@monotone_eight_corners true true true _ _ _); split; auto. }
  { apply (@monotone_eight_corners true true true _ _ _); split; auto. }
  { apply Z.mod_bound_min_max; auto. }
  { apply (@monotone_eight_corners true true true _ _ _); split; auto. }
  { auto with zarith. }
  { apply (@monotone_eight_corners false true false _ _ _); split; auto. }
  { apply (@monotone_eight_corners false true false _ _ _); split; auto. }
  { apply Z.mod_bound_min_max; auto. }
  { apply (@monotone_eight_corners false true false _ _ _); split; auto. }
  { auto with zarith. }
Qed.
