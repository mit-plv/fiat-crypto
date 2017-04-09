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
  unfold ZRange.is_bounded_by' in *; split; trivial.
  destruct x_bs as [lx ux], y_bs as [ly uy]; simpl in *.
  destruct Hboundedx as [Hboundedx _], Hboundedy as [Hboundedy _].
  pose proof (Hmonotone1 lx); pose proof (Hmonotone1 x); pose proof (Hmonotone1 ux).
  pose proof (Hmonotone2 ly); pose proof (Hmonotone2 y); pose proof (Hmonotone2 uy).
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
         end.
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

Local Notation stabilizes_after x l := (exists b, forall n, l < n -> Z.testbit x n = b).

Lemma stabilizes_after_Proper x
  : Proper (Z.le ==> Basics.impl) (fun l => stabilizes_after x l).
Proof.
  intros ?? H [b H']; exists b.
  intros n H''; apply (H' n); omega.
Qed.

Lemma stabilization_time (x:Z) : stabilizes_after x (Z.max (Z.log2 (Z.pred (- x))) (Z.log2 x)).
Proof.
  destruct (Z_lt_le_dec x 0); eexists; intros;
    [ eapply Z.bits_above_log2_neg | eapply Z.bits_above_log2]; lia.
Qed.

Lemma stabilization_time_weaker (x:Z) : stabilizes_after x (Z.log2_up (Z.abs x)).
Proof.
  eapply stabilizes_after_Proper; try apply stabilization_time.
  repeat match goal with
         | [ |- context[Z.abs _ ] ] => apply Zabs_ind; intro
         | [ |- context[Z.log2 ?x] ]
           => rewrite (Z.log2_nonpos x) by omega
         | [ |- context[Z.log2_up ?x] ]
           => rewrite (Z.log2_up_nonpos x) by omega
         | _ => rewrite Z.max_r by auto with zarith
         | _ => rewrite Z.max_l by auto with zarith
         | _ => etransitivity; [ apply Z.le_log2_log2_up | omega ]
         | _ => progress Z.replace_all_neg_with_pos
         | [ H : 0 <= ?x |- _ ]
           => assert (x = 0 \/ x = 1 \/ 1 < x) by omega; clear H; destruct_head' or; subst
         | _ => omega
         | _ => simpl; omega
         | _ => rewrite Z.log2_up_eqn by assumption
         | _ => progress change (Z.log2_up 1) with 0
         end.
Qed.

Lemma land_stabilizes (a b la lb:Z) (Ha:stabilizes_after a la) (Hb:stabilizes_after b lb) : stabilizes_after (Z.land a b) (Z.max la lb).
Proof.
  destruct Ha as [ba Hba]. destruct Hb as [bb Hbb].
  exists (andb ba bb); intros n Hn.
  rewrite Z.land_spec, Hba, Hbb; trivial; lia.
Qed.

Lemma lor_stabilizes (a b la lb:Z) (Ha:stabilizes_after a la) (Hb:stabilizes_after b lb) : stabilizes_after (Z.lor a b) (Z.max la lb).
Proof.
  destruct Ha as [ba Hba]. destruct Hb as [bb Hbb].
  exists (orb ba bb); intros n Hn.
  rewrite Z.lor_spec, Hba, Hbb; trivial; lia.
Qed.

Local Arguments Z.pow !_ !_.
Local Arguments Z.log2_up !_.
Local Arguments Z.add !_ !_.
Lemma stabilizes_bounded (x l:Z) (H:stabilizes_after x l) (Hl : 0 <= l) : Z.abs x <= 2^(1 + l) - 1.
Proof.
  rewrite Z.add_comm.
  destruct H as [b H].
  destruct (Z_zerop x); subst; simpl.
  { cut (0 < 2^(l + 1)); auto with zarith. }
  assert (Hlt : forall n, l < n <-> l + 1 <= n) by (intro; omega).
  apply Zabs_ind; intro.
  { pose proof (Z.testbit_false_bound x (l + 1)) as Hf.
    setoid_rewrite <- Z.le_ngt in Hf.
    setoid_rewrite <- Hlt in Hf.
    destruct b; specialize_by (omega || assumption); [ | omega ].
Admitted. (* this theorem statement is just a guess, I don't know what the actual bound is *)

Local Existing Instances Z.log2_up_le_Proper Z.add_le_Proper.
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
Local Existing Instances Z.add_le_Proper Z.sub_le_flip_le_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper Z.sub_le_eq_Proper.
Local Hint Extern 1 => progress cbv beta iota : typeclass_instances.
Lemma is_bounded_by_interp_op t tR (opc : op t tR)
      (bs : interp_flat_type Bounds.interp_base_type _)
      (v : interp_flat_type interp_base_type _)
      (H : Bounds.is_bounded_by bs v)
  : Bounds.is_bounded_by (Bounds.interp_op opc bs) (Syntax.interp_op _ _ opc v).
Proof.
  destruct opc; apply is_bounded_by_truncation_bounds;
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
  { apply monotone_four_corners_genb; try (split; auto);
      unfold Basics.flip;
      let x := fresh "x" in
      intro x;
        exists (0 <=? x);
        break_match; Z.ltb_to_lt;
          intros ???; nia. }
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
Qed.
