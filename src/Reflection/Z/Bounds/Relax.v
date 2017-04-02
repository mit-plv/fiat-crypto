Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.

Local Lemma helper logsz v
  : (v < 2 ^ 2 ^ Z.of_nat logsz)%Z <-> (Z.to_nat (Z.log2_up (Z.log2_up (1 + v))) <= logsz)%nat.
Proof.
  rewrite Nat2Z.inj_le, Z2Nat.id by auto with zarith.
  transitivity (1 + v <= 2^2^Z.of_nat logsz)%Z; [ omega | ].
  rewrite !Z.log2_up_le_pow2_full by auto with zarith.
  reflexivity.
Qed.

Local Arguments Z.pow : simpl never.
Local Arguments Z.sub !_ !_.
Local Arguments Z.add !_ !_.
Local Arguments Z.mul !_ !_.
Lemma relax_output_bounds'
      t (tight_output_bounds relaxed_output_bounds : interp_flat_type Bounds.interp_base_type t)
      (Hv : SmartFlatTypeMap (fun _ => Bounds.bounds_to_base_type) relaxed_output_bounds
            = SmartFlatTypeMap (fun _ => Bounds.bounds_to_base_type) tight_output_bounds)
      v k
      (v' := eq_rect _ (interp_flat_type _) v _ Hv)
      (Htighter : @Bounds.is_bounded_by
                    t tight_output_bounds
                    (@cast_back_flat_const
                       (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) tight_output_bounds
                       v')
                  /\ @cast_back_flat_const
                       (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) tight_output_bounds
                       v'
                     = k)
      (Hrelax : Bounds.is_tighter_thanb tight_output_bounds relaxed_output_bounds = true)
  : @Bounds.is_bounded_by
      t relaxed_output_bounds
      (@cast_back_flat_const
         (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) relaxed_output_bounds
         v)
    /\ @cast_back_flat_const
         (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) relaxed_output_bounds
         v
       = k.
Proof.
  destruct Htighter as [H0 H1]; subst v' k.
  cbv [Bounds.is_bounded_by cast_back_flat_const Bounds.is_tighter_thanb] in *.
  apply interp_flat_type_rel_pointwise_iff_relb in Hrelax.
  induction t; unfold SmartFlatTypeMap in *; simpl @smart_interp_flat_map in *; inversion_flat_type.
  { cbv [Bounds.is_tighter_thanb' ZRange.is_tighter_than_bool is_true SmartFlatTypeMap Bounds.bounds_to_base_type ZRange.is_bounded_by' ZRange.is_bounded_by Bounds.is_bounded_by' Bounds.bit_width_of_base_type] in *; simpl in *.
    repeat first [ progress inversion_flat_type
                 | progress inversion_base_type
                 | progress destruct_head bounds
                 | progress split_andb
                 | progress Z.ltb_to_lt
                 | progress break_match_hyps
                 | progress destruct_head'_and
                 | progress simpl in *
                 | rewrite helper in *
                 | omega
                 | tauto
                 | congruence
                 | progress destruct_head @eq; (reflexivity || omega)
                 | progress break_innermost_match_step
                 | apply conj ]. }
  { compute in *; tauto. }
  { simpl in *.
    specialize (fun Hv => IHt1 (fst tight_output_bounds) (fst relaxed_output_bounds) Hv (fst v)).
    specialize (fun Hv => IHt2 (snd tight_output_bounds) (snd relaxed_output_bounds) Hv (snd v)).
    do 2 match goal with
         | [ H : _ = _, H' : forall x, _ |- _ ] => specialize (H' H)
         end.
    simpl in *.
    split_and.
    repeat apply conj;
      [ match goal with H : _ |- _ => apply H end..
      | apply (f_equal2 (@pair _ _)); (etransitivity; [ match goal with H : _ |- _ => apply H end | ]) ];
      repeat first [ progress destruct_head prod
                   | progress simpl in *
                   | reflexivity
                   | assumption
                   | match goal with
                     | [ |- ?P (eq_rect _ _ _ _ _) = ?P _ ]
                       => apply f_equal; clear
                     | [ H : interp_flat_type_rel_pointwise (@Bounds.is_bounded_by') ?x ?y |- interp_flat_type_rel_pointwise (@Bounds.is_bounded_by') ?x ?y' ]
                       => clear -H;
                          match goal with |- ?R _ _ => generalize dependent R; intros end
                     | [ H : ?x = ?y |- _ ]
                       => first [ generalize dependent x | generalize dependent y ];
                          let k := fresh in intro k; intros; subst k
                     end ]. }
Qed.

Lemma relax_output_bounds
      t (tight_output_bounds relaxed_output_bounds : interp_flat_type Bounds.interp_base_type t)
      (Hv : SmartFlatTypeMap (fun _ => Bounds.bounds_to_base_type) relaxed_output_bounds
            = SmartFlatTypeMap (fun _ => Bounds.bounds_to_base_type) tight_output_bounds)
      v k
      (v' := eq_rect _ (interp_flat_type _) v _ Hv)
      (Htighter : @Bounds.is_bounded_by t tight_output_bounds k
                  /\ @cast_back_flat_const
                       (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) tight_output_bounds
                       v'
                     = k)
      (Hrelax : Bounds.is_tighter_thanb tight_output_bounds relaxed_output_bounds = true)
  : @Bounds.is_bounded_by t relaxed_output_bounds k
    /\ @cast_back_flat_const
         (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) relaxed_output_bounds
         v
       = k.
Proof.
  pose proof (fun pf => @relax_output_bounds' t tight_output_bounds relaxed_output_bounds Hv v k (conj pf (proj2 Htighter)) Hrelax) as H.
  destruct H as [H1 H2]; [ | rewrite <- H2; tauto ].
  subst v'.
  destruct Htighter; subst k; assumption.
Qed.
