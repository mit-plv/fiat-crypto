Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.Equality.
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
Local Existing Instances Z.pow_Zpos_le_Proper Z.log2_up_le_Proper.

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

  Local Ltac t_small :=
    repeat first [ progress cbv [Bounds.bounds_to_base_type Bounds.smallest_logsz Bounds.actual_logsz] in *
                 | progress simpl in *
                 | progress autorewrite with push_Zof_nat zsimplify_const
                 | solve [ trivial ]
                 | progress change (@interpToZ) with (fun t1 => cast_const (t1:=t1) (t2:=TZ)) in *
                 | progress change (@cast_const TZ TZ) with (fun x : Z => x) in *
                 | progress Z.ltb_to_lt
                 | rewrite Z2Nat.id in * by auto with zarith
                 | rewrite <- Z.log2_up_le_pow2_full in * by auto with zarith
                 | break_innermost_match_step
                 | apply conj
                 | omega
                 | rewrite <- Z.log2_up_le_full
                 | match goal with
                   | [ |- ?x < ?y ] => cut (x + 1 <= y); [ omega | ]
                   | [ H : (_ <=? _)%nat = true |- _ ] => apply Nat.leb_le in H
                   | [ H : (_ <= _)%nat |- _ ] => apply inj_le in H
                   end ].

  Local Arguments cast_const : simpl never.
  Lemma interpToZ_cast_const_small T0 (bs : Bounds.interp_base_type T0)
        (v : interp_base_type (@Bounds.bounds_to_base_type round_up T0 bs))
        (H : match Bounds.bit_width_of_base_type T0 with
             | Some sz => 0 <= ZRange.lower bs /\ ZRange.upper bs < 2 ^ sz
             | None => True
             end)
        (Hv : ZRange.lower bs <= interpToZ (cast_const (t2:=T0) v) <= ZRange.upper bs)
    : interpToZ (cast_const (t2:=T0) v) = interpToZ v.
  Proof.
    destruct_head base_type; simpl in *; try reflexivity.
    unfold Bounds.smallest_logsz, Bounds.interp_base_type, cast_const in *.
    break_innermost_match_hyps; Z.ltb_to_lt; simpl in *;
      [ pose proof (wordToZ_range v) | omega ].
    rewrite wordToZ_ZToWord_mod_full.
    rewrite wordToZ_ZToWord_mod_full in Hv.
    revert Hv; apply Z.max_case_strong; Z.rewrite_mod_small; intros; try omega; [].
    rewrite Z.mod_small; [ reflexivity | split; auto with zarith ].
    autorewrite with push_Zof_nat zsimplify_const in *.
    rewrite Z2Nat.id in * by auto with zarith.
    destruct_head' and.
    eapply Z.lt_le_trans; [ eassumption | ].
    repeat first [ progress Z.peel_le
                 | rewrite <- Z.log2_up_pow2 by auto with zarith; progress Z.peel_le
                 | omega ].
  Qed.

  Local Existing Instances Z.pow_Zpos_le_Proper Z.pow_Zpos_le_Proper_flip Z.lt_le_flip_Proper_flip_impl.
  Lemma ZToInterp_cast_const_small T (bs : Bounds.interp_base_type T)
        v
        (H : match Bounds.bit_width_of_base_type T with
             | Some sz => 0 <= ZRange.lower bs /\ ZRange.upper bs < 2 ^ sz
             | None => True
             end)
        (Hb : ZRange.lower bs <= interpToZ (@ZToInterp T v) <= ZRange.upper bs)
    : @cast_const (@Bounds.bounds_to_base_type round_up T bs) T (ZToInterp v) = ZToInterp v.
  Proof.
    apply ZToInterp_eq_inj.
    rewrite ?interpToZ_ZToInterp_mod.
    rewrite interpToZ_ZToInterp_mod in Hb.
    destruct T; simpl in *.
    { unfold Bounds.actual_logsz.
      break_innermost_match; Z.ltb_to_lt; try reflexivity; [].
      t_small.
      apply Z.max_case_strong; intros; Z.rewrite_mod_small; omega. }
    { unfold Bounds.smallest_logsz.
      break_innermost_match_step; Z.ltb_to_lt; try omega; [].
      revert Hb; apply (Z.max_case_strong 0 v); intros; Z.rewrite_mod_small; try reflexivity.
      rewrite Z.max_r by auto with zarith.
      autorewrite with push_Zof_nat zsimplify_const in *.
      rewrite Z2Nat.id by auto with zarith.
      rewrite Z.mod_mod_small; try apply conj; auto with zarith;
        repeat first [ rewrite <- Z.log2_up_le_pow2_full in * by auto with zarith
                     | rewrite <- Z.log2_up_le_full
                     | omega
                     | apply conj
                     | progress Z.peel_le
                     | rewrite <- Z.log2_up_pow2 by auto with zarith; progress Z.peel_le
                     | match goal with
                       | [ |- 2^?x mod 2^?y = 0 ]
                         => destruct (Z.pow2_lt_or_divides x y);
                            [ solve [ auto with zarith ]
                            | exfalso; assert (2^y <= 2^x)
                            | assumption ]
                       end ]. }
  Qed.

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
    generalize dependent (Bounds.interp_op opc bs); simpl; intros.
    repeat (destruct_one_head flat_type; try solve [ inversion opc ]);
      repeat first [ progress simpl in *
                   | progress destruct_head unit
                   | progress destruct_head True
                   | progress cbv [unzify_op cast_back_flat_const lift_op Bounds.is_bounded_by' ZRange.is_bounded_by'] in *
                   | progress change (@interpToZ TZ) with (fun x : Z => x) in *
                   | progress specialize_by auto
                   | progress specialize_by constructor
                   | match goal with
                     | [ H : forall v, _ <= ?f v <= _ /\ _ -> _ |- context[?f ?v'] ]
                       => specialize (H v')
                     | _ => progress specialize_by auto
                     | [ H : forall v : _ * _, _ /\ _ -> _ |- _ ]
                       => specialize (fun v1 v2 p1 p2 => H (v1, v2) (conj p1 p2));
                          cbn [fst snd] in H;
                          specialize (fun v1 p1 v2 p2 => H v1 v2 p1 p2)
                     end
                   | progress destruct_head'_and ];
      [
      | rewrite cast_const_idempotent_small by t_small; reflexivity
      | .. ];
      repeat match goal with
             | _ => progress change (@cast_const TZ) with @ZToInterp in *
             | [ |- context[@cast_const ?x TZ] ]
               => progress change (@cast_const x TZ) with (@interpToZ x) in *
             | [ H : context[@cast_const ?x TZ] |- _ ]
               => progress change (@cast_const x TZ) with (@interpToZ x) in *
             end;
      repeat match goal with
             | _ => reflexivity
             | _ => progress rewrite ?interpToZ_cast_const_small, ?ZToInterp_cast_const_small by auto
             | [ H : context[ZToInterp (?f (interpToZ (cast_const ?v)))] |- _ ]
               => rewrite (@interpToZ_cast_const_small _ _ v) in H by auto
             | [ H : context[(interpToZ (cast_const ?v), _)] |- _ ]
               => rewrite (@interpToZ_cast_const_small _ _ v) in H by auto
             | [ H : context[(_, interpToZ (cast_const ?v))] |- _ ]
               => rewrite (@interpToZ_cast_const_small _ _ v) in H by auto
             end.
  Qed.
End with_round_up.
