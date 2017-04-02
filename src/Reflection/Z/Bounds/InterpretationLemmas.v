Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).

Local Open Scope Z_scope.

Local Ltac break_t_step :=
  first [ progress destruct_head'_and
        | progress destruct_head'_or
        | progress destruct_head'_prod
        | progress split_andb
        | break_innermost_match_step ].

Local Ltac fin_t :=
  first [ reflexivity
        | assumption
        | match goal with
          | [ |- and _ _ ]
            => first [ split; [ | solve [ fin_t ] ]
                     | split; [ solve [ fin_t ] | ] ];
               try solve [ fin_t ]
          end
        | omega ].

Local Ltac specializer_t_step :=
  first [ progress specialize_by_assumption
        | progress specialize_by fin_t ].

Local Ltac Zarith_t_step :=
  first [ match goal with
          | [ H : (?x <= ?y)%Z, H' : (?y <= ?x)%Z |- _ ]
            => assert (x = y) by omega; clear H H'
          end
        | progress Z.ltb_to_lt_in_context ].
Local Ltac Zarith_land_lor_t_step :=
  match goal with
  | [ |- _ <= Z.lor _ _ <= _ ]
    => split; etransitivity; [ | apply Z.lor_bounds; omega | apply Z.lor_bounds; omega | ]
  | [ |- 2^Z.log2_up (?x + 1) - 1 <= 2^Z.log2_up (?y + 1) - 1 ]
    => let H := fresh in assert (H : x <= y) by omega; rewrite H; reflexivity
  end.
Local Ltac word_arith_t :=
  match goal with
  | [ |- (0 <= FixedWordSizes.wordToZ ?w <= 2^2^Z.of_nat ?logsz - 1)%Z ]
    => clear; pose proof (@wordToZ_range logsz w); autorewrite with push_Zof_nat zsimplify_const in *; try omega
  end.

Local Ltac revert_min_max :=
  repeat match goal with
         | [ H : context[Z.min _ _] |- _ ] => revert H
         | [ H : context[Z.max _ _] |- _ ] => revert H
         end.
Local Ltac split_min_max :=
  repeat match goal with
         | [ H : (?a <= ?b)%Z |- context[Z.max ?a ?b] ]
           => rewrite (Z.max_r a b) by omega
         | [ H : (?b <= ?a)%Z |- context[Z.max ?a ?b] ]
           => rewrite (Z.max_l a b) by omega
         | [ H : (?a <= ?b)%Z |- context[Z.min ?a ?b] ]
           => rewrite (Z.min_l a b) by omega
         | [ H : (?b <= ?a)%Z |- context[Z.min ?a ?b] ]
           => rewrite (Z.min_r a b) by omega
         | [ |- context[Z.max ?a ?b] ]
           => first [ rewrite (Z.max_l a b) by omega
                    | rewrite (Z.max_r a b) by omega ]
         | [ |- context[Z.min ?a ?b] ]
           => first [ rewrite (Z.min_l a b) by omega
                    | rewrite (Z.min_r a b) by omega ]
         | _ => revert_min_max; progress repeat apply Z.min_case_strong; intros
         | _ => revert_min_max; progress repeat apply Z.max_case_strong; intros
         end.

Local Ltac case_Zvar_nonneg_on x :=
  is_var x;
  lazymatch type of x with
  | Z => lazymatch goal with
         | [ H : (0 <= x)%Z |- _ ] => fail
         | [ H : (x < 0)%Z |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0); try omega
         end
  end.
Local Ltac case_Zvar_nonneg_step :=
  match goal with
  | [ |- context[?x] ]
    => case_Zvar_nonneg_on x
  end.
Local Ltac case_Zvar_nonneg := repeat case_Zvar_nonneg_step.

Local Ltac remove_binary_operation_le_hyps_step :=
  match goal with
  | [ H : (?f ?x ?y <= ?f ?x ?y')%Z |- _ ]
    => assert ((y = y') \/ (y < y' /\ 0 <= x))%Z by (assert (y <= y')%Z by omega; nia);
       clear H
  | [ H : (?f ?y ?x <= ?f ?y' ?x)%Z |- _ ]
    => assert ((y = y') \/ (y < y' /\ 0 <= x))%Z by (assert (y <= y')%Z by omega; nia);
       clear H
  | [ H : (?f ?x ?y <= ?f ?x ?y')%Z |- _ ]
    => assert ((y = y') \/ (y' < y /\ x <= 0))%Z by (assert (y' <= y)%Z by omega; nia);
       clear H
  | [ H : (?f ?y ?x <= ?f ?y' ?x)%Z |- _ ]
    => assert ((y = y') \/ (y' < y /\ x <= 0))%Z by (assert (y' <= y)%Z by omega; nia);
       clear H
  | [ H : ?T, H' : ?T |- _ ] => clear H'
  | [ H : ?A \/ (~?A /\ ?B), H' : ?A \/ (~?A /\ ?C) |- _ ]
    => assert (A \/ (~A /\ (B /\ C))) by (clear -H H'; tauto); clear H H'
  | _ => progress destruct_head' or; destruct_head' and; subst; try omega
  | [ |- (_ <= _ <= _)%Z ] => split
  | _ => case_Zvar_nonneg_step
  end.

Local Ltac saturate_with_shift_facts :=
  repeat match goal with
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?x << ?x'] ]
           => unique assert (x << x' <= y << y') by (apply Z.shiftl_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?y << ?y'] ]
           => unique assert (x << x' <= y << y') by (apply Z.shiftl_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?x >> ?x'] ]
           => unique assert (x >> x' <= y >> y') by (apply Z.shiftr_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?y >> ?y'] ]
           => unique assert (x >> x' <= y >> y') by (apply Z.shiftr_le_mono; omega)
         end.
Local Ltac saturate_with_all_shift_facts :=
  repeat match goal with
         | _ => progress saturate_with_shift_facts
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[Z.shiftl _ _] ]
           => unique assert (x << x' <= y << y') by (apply Z.shiftl_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[Z.shiftr _ _] ]
           => unique assert (x >> x' <= y >> y') by (apply Z.shiftr_le_mono; omega)
         end.
Local Ltac saturate_land_lor_facts :=
  repeat match goal with
         | [ |- context[Z.land ?x ?y] ]
           => let H := fresh in
              let H' := fresh in
              assert (H : 0 <= x) by omega;
              assert (H' : 0 <= y) by omega;
              unique pose proof (Z.land_upper_bound_r x y H H');
              unique pose proof (Z.land_upper_bound_l x y H H')
         | [ |- context[Z.land ?x ?y] ]
           => unique assert (0 <= Z.land x y) by (apply Z.land_nonneg; omega)
         | [ |- context[Z.land ?x ?y] ]
           => case_Zvar_nonneg_on x; case_Zvar_nonneg_on y
         | [ |- context[Z.lor ?x ?y] ]
           => let H := fresh in
              let H' := fresh in
              assert (H : 0 <= x) by omega;
              assert (H' : 0 <= y) by omega;
              unique pose proof (proj1 (Z.lor_bounds x y H H'));
              unique pose proof (proj2 (Z.lor_bounds x y H H'))
         | [ |- context[Z.lor ?x ?y] ]
           => unique assert (0 <= Z.lor x y) by (apply Z.lor_nonneg; omega)
         | [ |- context[Z.lor ?x ?y] ]
           => case_Zvar_nonneg_on x; case_Zvar_nonneg_on y
         end.
Local Ltac clean_neg :=
  repeat match goal with
         | [ H : (-?x) < 0 |- _ ] => assert (0 <= x) by omega; assert (x <> 0) by omega; clear H
         | [ H : -?x <= -?y |- _ ] => apply Z.opp_le_mono in H
         | [ |- -?x <= -?y ] => apply Z.opp_le_mono
         | _ => progress rewrite <- Z.opp_le_mono in *
         end.
Local Ltac replace_with_neg x :=
  assert (x = -(-x)) by omega; generalize dependent (-x);
  let x' := fresh in
  rename x into x'; intro x; intros; subst x';
  clean_neg.
Local Ltac replace_all_neg_with_pos :=
  repeat match goal with
         | [ H : ?x < 0 |- _ ] => replace_with_neg x
         end.
Local Ltac handle_shift_neg :=
  repeat first [ rewrite !Z.shiftr_opp_r
               | rewrite !Z.shiftl_opp_r ].

Local Ltac handle_four_corners_step_fast :=
  first [ progress destruct_head Bounds.t
        | progress cbv [Bounds.four_corners] in *
        | progress subst
        | Zarith_t_step
        | progress split_min_max
        | omega
        | nia ].
Local Ltac handle_four_corners_step :=
  first [ handle_four_corners_step_fast
        | remove_binary_operation_le_hyps_step ].
Local Ltac handle_four_corners :=
  lazymatch goal with
  | [ |- (ZRange.lower (Bounds.four_corners _ _ _) <= _ <= _)%Z ]
    => idtac
  end;
  repeat handle_four_corners_step.

Local Ltac rewriter_t :=
  first [ rewrite !Bool.andb_true_iff
        | rewrite !Bool.andb_false_iff
        | rewrite !Bool.orb_true_iff
        | rewrite !Bool.orb_false_iff
        | rewrite !Z.abs_opp
        | rewrite !Z.max_log2_up
        | rewrite !Z.add_max_distr_r
        | rewrite !Z.add_max_distr_l
        | rewrite wordToZ_ZToWord by (autorewrite with push_Zof_nat zsimplify_const; omega)
        | match goal with
          | [ H : _ |- _ ]
            => first [ rewrite !Bool.andb_true_iff in H
                     | rewrite !Bool.andb_false_iff in H
                     | rewrite !Bool.orb_true_iff in H
                     | rewrite !Bool.orb_false_iff in H ]
          end ].

Local Arguments Bounds.is_bounded_by' !_ _ _ / .

Lemma is_bounded_by_truncation_bounds Tout bs v
      (H : Bounds.is_bounded_by (T:=Tbase TZ) bs v)
  : Bounds.is_bounded_by (T:=Tbase Tout)
                         (Bounds.truncation_bounds (Bounds.bit_width_of_base_type Tout) bs)
                         (ZToInterp v).
Proof.
  destruct bs as [l u]; cbv [Bounds.truncation_bounds Bounds.is_bounded_by Bounds.is_bounded_by' Bounds.bit_width_of_base_type ZRange.is_bounded_by'] in *; simpl in *.
  repeat first [ break_t_step
               | fin_t
               | progress simpl in *
               | Zarith_t_step
               | rewriter_t
               | word_arith_t ].
Qed.

Local Ltac t_special_case_op_step :=
  first [ fin_t
        | progress intros
        | progress subst
        | progress simpl in *
        | progress split_andb
        | progress Zarith_t_step
        | specializer_t_step
        | rewriter_t
        | progress break_t_step
        | progress split_min_max
        | progress cbv [Bounds.neg' Bounds.cmovne' Bounds.cmovle' ModularBaseSystemListZOperations.neg ModularBaseSystemListZOperations.cmovne ModularBaseSystemListZOperations.cmovl] ].
Local Ltac t_special_case_op := repeat t_special_case_op_step.

Local Arguments Z.pow : simpl never.
Local Arguments Z.add !_ !_.
Local Existing Instances Z.add_le_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper Z.sub_le_eq_Proper.
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
  { handle_four_corners. }
  { handle_four_corners. }
  { handle_four_corners. }
  { destruct_head Bounds.t.
    case_Zvar_nonneg; replace_all_neg_with_pos; handle_shift_neg;
      autorewrite with Zshift_to_pow;
      rewrite ?Z.div_opp_l_complete by auto with zarith;
      autorewrite with Zpow_to_shift.
    16:split_min_max; saturate_with_shift_facts; omega.
    all:admit. }
  { destruct_head Bounds.t.
    case_Zvar_nonneg; replace_all_neg_with_pos; handle_shift_neg; admit. }
  { repeat first [ progress destruct_head Bounds.t
                 | progress simpl in *
                 | break_t_step
                 | Zarith_t_step
                 | rewriter_t
                 | progress replace_all_neg_with_pos
                 | progress saturate_land_lor_facts
                 | split_min_max; omega ];
      admit. }
  { repeat first [ progress destruct_head Bounds.t
                 | progress simpl in *
                 | break_t_step
                 | Zarith_t_step
                 | rewriter_t
                 | progress replace_all_neg_with_pos
                 | progress saturate_land_lor_facts
                 | progress Zarith_land_lor_t_step
                 | solve [ split_min_max; try omega; try Zarith_land_lor_t_step ] ];
      admit. }
  { t_special_case_op. }
  { t_special_case_op. }
  { t_special_case_op. }
Admitted.

Local Arguments lift_op : simpl never.
Local Arguments cast_back_flat_const : simpl never.
Local Arguments unzify_op : simpl never.
Local Arguments Z.pow : simpl never.
Local Arguments Z.add !_ !_.
Local Existing Instance Z.pow_Zpos_le_Proper.
Lemma pull_cast_genericize_op t tR (opc : op t tR)
      (bs : interp_flat_type Bounds.interp_base_type t)
      (v : interp_flat_type interp_base_type (pick_type bs))
      (H : Bounds.is_bounded_by bs
                                (SmartFlatTypeMapUnInterp
                                   (fun (t1 : base_type) (b0 : Bounds.interp_base_type t1) => cast_const) v))
  : interp_op t tR opc (cast_back_flat_const v)
    = cast_back_flat_const (interp_op (pick_type bs) (pick_type (Bounds.interp_op opc bs)) (genericize_op opc) v).
Proof.
  pose proof (is_bounded_by_interp_op t tR opc bs).
  unfold interp_op in *.
  rewrite Zinterp_op_genericize_op.
  generalize dependent (Zinterp_op t tR opc).
  generalize dependent (Bounds.interp_op opc bs); clear opc; simpl; intros.
  revert dependent t; induction tR as [tR| |]; intros;
    [
    | repeat first [ match goal with
                     | [ |- ?x = ?y ]
                       => transitivity tt; destruct x, y; reflexivity
                     end
                   | reflexivity
                   | progress simpl @Bounds.is_bounded_by in *
                   | rewrite !lift_op_prod_dst
                   | rewrite !cast_back_flat_const_prod
                   | progress split_and
                   | match goal with
                     | [ H : _ |- _ ] => first [ setoid_rewrite lift_op_prod_dst in H
                                               | setoid_rewrite cast_back_flat_const_prod in H ]
                     end
                   | setoid_rewrite lift_op_prod_dst
                   | match goal with
                     | [ H : _ |- _ ] => erewrite H by eassumption
                     end ].. ].
  revert dependent tR; induction t as [t| |]; intros;
    [
    | repeat first [ match goal with
                     | [ |- ?x = ?y ]
                       => transitivity tt; destruct x, y; reflexivity
                     end
                   | reflexivity
                   | progress simpl @Bounds.is_bounded_by in *
                   | rewrite !lift_op_prod_dst
                   | rewrite !cast_back_flat_const_prod
                   | progress split_and
                   | match goal with
                     | [ H : _ |- _ ] => first [ setoid_rewrite lift_op_prod_dst in H
                                               | setoid_rewrite cast_back_flat_const_prod in H ]
                     end
                   | setoid_rewrite lift_op_prod_dst
                   | match goal with
                     | [ H : _ |- _ ] => erewrite H by eassumption
                     end ].. ].
  { simpl in *; unfold unzify_op, cast_back_flat_const, SmartFlatTypeMap, Bounds.interp_base_type, cast_const, Bounds.is_bounded_by', lift_op, SmartFlatTypeMapUnInterp, SmartFlatTypeMapInterp2, cast_const in *; simpl in *.
    unfold Bounds.is_bounded_by', cast_const, ZToInterp, interpToZ, Bounds.bounds_to_base_type, ZRange.is_bounded_by' in *; simpl in *.
    destruct_head base_type; break_innermost_match; Z.ltb_to_lt; destruct_head Bounds.t;
      repeat match goal with
             | _ => progress destruct_head'_and
             | _ => reflexivity
             | [ H : forall v, _ /\ True -> _ |- _ ] => specialize (fun v pf => H v (conj pf I))
             | [ H : forall v, _ -> _ /\ True |- _ ] => pose proof (fun v pf => proj1 (H v pf)); clear H
             | [ H : True |- _ ] => clear H
             | [ H : ?T, H' : ?T |- _ ] => clear H
             | [ H : forall v, _ -> _ <= ?f v <= _ |- ?f ?v' = _ ]
               => specialize (H v')
             | [ H : forall v, _ -> _ <= ?f (?g v) <= _ |- ?f (?g ?v') = _ ]
               => specialize (H v')
             | [ H : forall v, _ -> _ <= ?f (?g (?h v)) <= _ /\ _ /\ _ |- context[?h ?v'] ]
               => specialize (H v')
             | [ H : forall v, _ -> _ <= ?f (?g (?h (?i v))) <= _ /\ _ /\ _ |- context[?h (?i ?v')] ]
               => specialize (H v')
             | _ => progress specialize_by omega
             | _ => rewrite wordToZ_ZToWord
                 by repeat match goal with
                           | [ |- and _ _ ] => split
                           | [ |- ?x < ?y ] => cut (1 + x <= y); [ omega | ]
                           | _ => omega
                           | _ => progress autorewrite with push_Zof_nat zsimplify_const
                           | _ => rewrite Z2Nat.id by auto with zarith
                           | _ => rewrite <- !Z.log2_up_le_full
                           end
             | _ => rewrite wordToZ_ZToWord in *
                 by repeat match goal with
                           | [ |- and _ _ ] => split
                           | [ |- ?x < ?y ] => cut (1 + x <= y); [ omega | ]
                           | _ => omega
                           | _ => progress autorewrite with push_Zof_nat zsimplify_const
                           | _ => rewrite Z2Nat.id by auto with zarith
                           | _ => rewrite <- !Z.log2_up_le_full
                           end
             | _ => rewrite wordToZ_ZToWord_wordToZ
                 by (rewrite Nat2Z.inj_le, Z2Nat.id, <- !Z.log2_up_le_pow2_full by auto with zarith; omega)
             | _ => rewrite wordToZ_ZToWord_wordToZ in *
                 by (rewrite Nat2Z.inj_le, Z2Nat.id, <- !Z.log2_up_le_pow2_full by auto with zarith; omega)
             end.
    all:admit. }
  { simpl in *.
    specialize (H0 tt I).
    simpl in *.
    hnf in H0.
    unfold cast_back_flat_const, lift_op, unzify_op in *; simpl in *.
    unfold interpToZ in *.
    unfold Bounds.bounds_to_base_type in *.
    destruct_head base_type; simpl in *.
    split_andb.
    Z.ltb_to_lt.
    all:destruct_head' and.
    all:simpl in *.
    all:break_innermost_match; break_match_hyps; split_andb; Z.ltb_to_lt; try reflexivity.
    all:try (simpl in *;
    rewrite wordToZ_ZToWord
      by (autorewrite with push_Zof_nat zsimplify_const;
        rewrite Z2Nat.id by auto with zarith;
        split; try omega;
        match goal with
        | [ |- (?x < ?y)%Z ]
          => apply (Z.lt_le_trans x (x + 1) y); [ omega | ]
        end;
        rewrite <- !Z.log2_up_le_full;
        omega)).
    all:try reflexivity.
    unfold interpToZ, cast_const.
    simpl.
    rewrite ZToWord_wordToZ_ZToWord; [ reflexivity | ].
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id by auto with zarith.

Admitted.
