Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.Tactics.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Util.ZRange.CornersMonotoneBounds.
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
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.

Local Open Scope Z_scope.

Local Arguments Bounds.is_bounded_by' !_ _ _ / .

Lemma is_bounded_by_truncation_bounds' Tout bs v
      (H : Bounds.is_bounded_by (T:=Tbase TZ) bs v)
  : Bounds.is_bounded_by (T:=Tbase Tout)
                         (Bounds.truncation_bounds' (Bounds.bit_width_of_base_type Tout) bs)
                         (ZToInterp v).
Proof.
  destruct bs as [l u]; cbv [Bounds.truncation_bounds' Bounds.is_bounded_by Bounds.is_bounded_by' Bounds.bit_width_of_base_type Bounds.log_bit_width_of_base_type option_map ZRange.is_bounded_by'] in *; simpl in *.
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
  apply ZRange.monotonify2; auto;
    unfold Bounds.extreme_lor_land_bounds;
    [ apply land_upper_lor_land_bounds
    | apply upper_lor_and_bounds_Proper ].
Qed.
Lemma lor_bounds_extreme xb yb x y
      (Hx : ZRange.is_bounded_by' None xb x)
      (Hy : ZRange.is_bounded_by' None yb y)
  : ZRange.is_bounded_by' None (Bounds.extreme_lor_land_bounds xb yb) (Z.lor x y).
Proof.
  apply ZRange.monotonify2; auto;
    unfold Bounds.extreme_lor_land_bounds;
    [ apply lor_upper_lor_land_bounds
    | apply upper_lor_and_bounds_Proper ].
Qed.

Local Arguments N.ldiff : simpl never.
Local Arguments Z.pow : simpl never.
Local Arguments Z.add !_ !_.
Local Existing Instances Z.add_le_Proper Z.sub_le_flip_le_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper Z.sub_le_eq_Proper Z.add_with_carry_le_Proper.
Local Hint Extern 1 => progress cbv beta iota : typeclass_instances.
Local Ltac ibbio_prefin :=
  [ > | intros | simpl; reflexivity ].
Local Ltac apply_is_bounded_by_truncation_bounds :=
  cbv [id
         Bounds.interp_op interp_op Bounds.is_bounded_by Relations.interp_flat_type_rel_pointwise Relations.interp_flat_type_rel_pointwise_gen_Prop SmartVarfMap smart_interp_flat_map lift_op SmartFlatTypeMapUnInterp cast_const Zinterp_op SmartFlatTypeMapInterp2
         Z.add_with_get_carry Bounds.add_with_get_carry Bounds.sub_with_get_borrow Bounds.get_carry Bounds.get_borrow Z.get_carry Bounds.mul_split];
  cbn [interpToZ fst snd];
  repeat match goal with
         | [ |- _ /\ _ ] => split
         end;
  lazymatch goal with
  | [ |- Bounds.is_bounded_by' (Bounds.truncation_bounds _ _) (ZToInterp _) ]
    => apply is_bounded_by_truncation_bounds'
  end.
Local Ltac handle_mul :=
  apply ZRange.monotone_four_corners_genb; try (split; auto);
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
  destruct opc; apply_is_bounded_by_truncation_bounds;
    [ ..
    | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v mod _)) (v:=ZToInterp _);
      [ .. | cbn -[Z.mul_split_at_bitwidth]; rewrite Z.mul_split_at_bitwidth_mod ];
      ibbio_prefin
    | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v / _))   (v:=ZToInterp _);
        [ .. | cbn -[Z.mul_split_at_bitwidth]; rewrite Z.mul_split_at_bitwidth_div ];
        ibbio_prefin
    |
    | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v mod _)) (v:=ZToInterp _);
        ibbio_prefin
    | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v / _))   (v:=ZToInterp _);
        ibbio_prefin
    |
    | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (v mod _)) (v:=ZToInterp _);
        ibbio_prefin
    | eapply is_bounded_by_compose with (T1:=TZ) (f_v := fun v => ZToInterp (-(v / _)))   (v:=ZToInterp _);
      ibbio_prefin ];
    repeat first [ progress simpl in *
                 | progress cbv [Bounds.interp_base_type Bounds.is_bounded_by' ZRange.is_bounded_by'] in *
                 | progress destruct_head'_prod
                 | progress destruct_head'_and
                 | omega
                 | match goal with
                   | [ |- context[interpToZ ?x] ]
                     => generalize dependent (interpToZ x); clear x; intros
                   | [ |- _ /\ True ] => split; [ | tauto ]
                   end ].
  { apply (@ZRange.monotone_four_corners true true _ _); split; auto. }
  { apply (@ZRange.monotone_four_corners true false _ _); split; auto. }
  { handle_mul. }
  { apply ZRange.monotone_four_corners_genb; try (split; auto);
      [ eexists; apply Z.shiftl_le_Proper1
      | exists true; apply Z.shiftl_le_Proper2 ]. }
  { apply ZRange.monotone_four_corners_genb; try (split; auto);
      [ eexists; apply Z.shiftr_le_Proper1
      | exists true; apply Z.shiftr_le_Proper2 ]. }
  { cbv [Bounds.land Bounds.extremization_bounds]; break_innermost_match;
      [ apply land_bounds_extreme; split; auto | .. ];
      repeat first [ progress simpl in *
                   | Zarith_t_step
                   | rewriter_t
                   | progress saturate_land_lor_facts
                   | split_min_max; omega ]. }
  { cbv [Bounds.lor Bounds.extremization_bounds]; break_innermost_match;
      [ apply lor_bounds_extreme; split; auto | .. ];
      repeat first [ progress simpl in *
                   | Zarith_t_step
                   | rewriter_t
                   | progress Zarith_land_lor_t_step
                   | solve [ split_min_max; try omega; try Zarith_land_lor_t_step ] ]. }
  { repeat first [ progress destruct_head Bounds.t
                 | progress simpl in *
                 | progress split_min_max
                 | omega ]. }
  { cbv [Bounds.id_with_alt];
      break_innermost_match; simpl in *; Z.ltb_to_lt; subst;
        split; assumption. }
  { destruct_head Bounds.t; cbv [Bounds.zselect' Z.zselect].
    break_innermost_match; split_min_max; omega. }
  { handle_mul. }
  { apply Z.mod_bound_min_max; auto. }
  { handle_mul. }
  { auto with zarith. }
  { apply (@ZRange.monotone_eight_corners true true true _ _ _); split; auto. }
  { apply (@ZRange.monotone_eight_corners true true true _ _ _); split; auto. }
  { apply Z.mod_bound_min_max; auto. }
  { apply (@ZRange.monotone_eight_corners true true true _ _ _); split; auto. }
  { auto with zarith. }
  { apply (@ZRange.monotone_eight_corners false true false _ _ _); split; auto. }
  { apply (@ZRange.monotone_eight_corners false true false _ _ _); split; auto. }
  { apply Z.mod_bound_min_max; auto. }
  { apply (@ZRange.monotone_eight_corners false true false _ _ _); split; auto. }
  { auto with zarith. }
Qed.
