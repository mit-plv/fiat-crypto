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
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.

Local Open Scope Z_scope.

Local Arguments lift_op : simpl never.
Local Arguments cast_back_flat_const : simpl never.
Local Arguments unzify_op : simpl never.
Local Arguments Z.pow : simpl never.
Local Arguments Z.add !_ !_.
Local Existing Instance Z.pow_Zpos_le_Proper.

Section with_round_up.
  Context (is_bounded_by_interp_op
           : forall t tR (opc : op t tR)
                    (bs : interp_flat_type Bounds.interp_base_type _)
                    (v : interp_flat_type interp_base_type _)
                    (H : Bounds.is_bounded_by bs v),
              Bounds.is_bounded_by (Bounds.interp_op opc bs) (Syntax.interp_op _ _ opc v)).
  Context {round_up : nat -> option nat}.

  Local Notation pick_typeb := (@Bounds.bounds_to_base_type round_up) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).

  Lemma pull_cast_genericize_op
        t tR (opc : op t tR)
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

  Admitted.
End with_round_up.
