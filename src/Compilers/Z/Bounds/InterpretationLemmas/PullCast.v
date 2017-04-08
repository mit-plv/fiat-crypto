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
      | ];
      repeat match goal with
             | _ => progress change (@cast_const TZ) with @ZToInterp in *
             | [ |- context[@cast_const ?x TZ] ]
               => progress change (@cast_const x TZ) with (@interpToZ x) in *
             | [ H : context[@cast_const ?x TZ] |- _ ]
               => progress change (@cast_const x TZ) with (@interpToZ x) in *
             end.
    all:repeat match goal with
               | [ H : _ |- _ ] => progress rewrite ?cast_const_ZToInterp_mod, ?interpToZ_cast_const_mod, ?interpToZ_ZToInterp_mod in H
               | _ => progress rewrite ?cast_const_ZToInterp_mod, ?interpToZ_cast_const_mod, ?interpToZ_ZToInterp_mod
               | [ |- ZToInterp _ = ZToInterp _ ]
                 => apply ZToInterp_eq_inj
               | [ |- context[interpToZ ?x] ]
                 => is_var x; pose proof (interpToZ_range x); generalize dependent (interpToZ x);
                      clear x; intro x; intros
               end.
    { repeat first [ reflexivity
                   | progress subst
                   | progress Z.ltb_to_lt
                   | progress inversion_base_type_constr
                   | progress destruct_head'_and
                   | omega
                   | break_innermost_match_step
                   | progress cbv [Bounds.bit_width_of_base_type option_map Bounds.log_bit_width_of_base_type] in *
                   | rewrite Z2Nat.id in * by auto with zarith
                   | rewrite <- Z.log2_up_le_pow2_full in * by auto with zarith
                   | progress autorewrite with push_Zof_nat zsimplify_const
                   | progress intros
                   | match goal with
                     | [ H : Bounds.bounds_to_base_type _ ?x = _, H' : ZRange.lower ?x <= ?v |- context[?v] ]
                       => cbv [Bounds.actual_logsz Bounds.bounds_to_base_type] in H; revert H
                     | [ H : (_ <=? _)%nat = true |- _ ] => apply Nat.leb_le in H
                     | [ H : (_ <= _)%nat |- _ ] => apply inj_le in H
                     | [ H : ?x <= 0, H' : 0 <= ?x |- _ ] => assert (x = 0) by omega; clear H H'
                     | [ |- context[Z.max 0 ?x] ]
                       => repeat match goal with
                                 | [ H : context[Z.max 0 x] |- _ ] => revert H
                                 end;
                          apply Z.max_case_strong; Z.rewrite_mod_small; intros
                     end ].
      all:repeat first [ reflexivity
                   | progress subst
                   | progress Z.ltb_to_lt
                   | progress inversion_base_type_constr
                   | progress destruct_head'_and
                   | omega
                   | break_innermost_match_step
                   | progress cbv [Bounds.bit_width_of_base_type option_map Bounds.log_bit_width_of_base_type] in *
                   | rewrite Z2Nat.id in * by auto with zarith
                   | rewrite <- Z.log2_up_le_pow2_full in * by auto with zarith
                   | progress autorewrite with push_Zof_nat zsimplify_const
                   | progress intros
                   | match goal with
                     | [ H : Bounds.bounds_to_base_type _ ?x = _, H' : ZRange.lower ?x <= ?v |- context[?v] ]
                       => cbv [Bounds.actual_logsz Bounds.bounds_to_base_type] in H; revert H
                     | [ H : (_ <=? _)%nat = true |- _ ] => apply Nat.leb_le in H
                     | [ H : (_ <= _)%nat |- _ ] => apply inj_le in H
                     | [ H : ?x <= 0, H' : 0 <= ?x |- _ ] => assert (x = 0) by omega; clear H H'
                     | [ |- context[Z.max 0 ?x] ]
                       => repeat match goal with
                                 | [ H : context[Z.max 0 x] |- _ ] => revert H
                                 end;
                          apply Z.max_case_strong; Z.rewrite_mod_small; intros
                     end
                   | progress cbv [Bounds.bounds_to_base_type Bounds.smallest_logsz] in *
                   | progress break_innermost_match_hyps_step
                   | progress autorewrite with push_Zof_nat zsimplify_const in * ].
      all:repeat first [ reflexivity
                       | progress subst
                       | progress Z.ltb_to_lt
                       | progress inversion_base_type_constr
                       | progress destruct_head'_and
                       | omega
                       | break_innermost_match_step
                       | progress cbv [Bounds.bit_width_of_base_type option_map Bounds.log_bit_width_of_base_type] in *
                       | rewrite Z2Nat.id in * by auto with zarith
                       | rewrite <- Z.log2_up_le_pow2_full in * by auto with zarith
                       | rewrite <- Z.log2_up_le_full in *
                       | rewrite Z.log2_up_pow2 in * by auto with zarith
                       | progress autorewrite with push_Zof_nat zsimplify_const
                       | progress intros
                       | match goal with
                         | [ H : Bounds.bounds_to_base_type _ ?x = _, H' : ZRange.lower ?x <= ?v |- context[?v] ]
                           => cbv [Bounds.actual_logsz Bounds.bounds_to_base_type] in H; revert H
                         | [ H : (_ <=? _)%nat = true |- _ ] => apply Nat.leb_le in H
                         | [ H : (_ <= _)%nat |- _ ] => apply inj_le in H
                         | [ H : ?x <= 0, H' : 0 <= ?x |- _ ] => assert (x = 0) by omega; clear H H'
                         | [ |- ?x < ?y ] => cut (1 + x <= y); [ omega | ]
                         | [ H : ?x < ?y |- _ ] => assert (1 + x <= y) by omega; clear H
                         | [ |- context[Z.max 0 ?x] ]
                           => repeat match goal with
                                     | [ H : context[Z.max 0 x] |- _ ] => revert H
                                     end;
                              apply Z.max_case_strong; Z.rewrite_mod_small; intros
                         end
                       | progress cbv [Bounds.bounds_to_base_type Bounds.smallest_logsz Bounds.actual_logsz] in *
                       | progress break_innermost_match_hyps_step
                       | progress autorewrite with push_Zof_nat zsimplify_const in *
                       | match goal with
                         | [ H : ?x <= 2^2^Z.log2_up (Z.log2_up ?y), H' : ?y <= 2^2^?z |- context[_ mod 2^2^?z] ]
                           => rewrite H' in H
                         end
                       | progress Z.rewrite_mod_small ].
      all:repeat first [ reflexivity
                       | progress subst
                       | progress Z.ltb_to_lt
                       | progress inversion_base_type_constr
                       | progress inversion_option
                       | progress destruct_head'_and
                       | omega
                       | break_innermost_match_step
                       | progress cbv [Bounds.bit_width_of_base_type option_map Bounds.log_bit_width_of_base_type] in *
                       | rewrite Z2Nat.id in * by auto with zarith
                       | rewrite <- Z.log2_up_le_pow2_full in * by auto with zarith
                       | rewrite <- Z.log2_up_le_full in *
                       | rewrite Z.log2_up_pow2 in * by auto with zarith
                       | progress autorewrite with push_Zof_nat zsimplify_const
                       | progress intros
                       | match goal with
                         | [ H : Bounds.bounds_to_base_type _ ?x = _, H' : ZRange.lower ?x <= ?v |- context[?v] ]
                           => cbv [Bounds.actual_logsz Bounds.bounds_to_base_type] in H; revert H
                         | [ H : (_ <=? _)%nat = true |- _ ] => apply Nat.leb_le in H
                         | [ H : (_ <= _)%nat |- _ ] => apply inj_le in H
                         | [ H : ?x <= 0, H' : 0 <= ?x |- _ ] => assert (x = 0) by omega; clear H H'
                         | [ |- ?x < ?y ] => cut (1 + x <= y); [ omega | ]
                         | [ H : ?x < ?y |- _ ] => assert (1 + x <= y) by omega; clear H
                         | [ |- context[Z.max 0 ?x] ]
                           => repeat match goal with
                                     | [ H : context[Z.max 0 x] |- _ ] => revert H
                                     end;
                              apply Z.max_case_strong; Z.rewrite_mod_small; intros
                         end
                       | progress cbv [Bounds.bounds_to_base_type Bounds.smallest_logsz Bounds.actual_logsz] in *
                       | progress break_innermost_match_hyps_step
                       | progress autorewrite with push_Zof_nat zsimplify_const in *
                       | match goal with
                         | [ H : ?x <= 2^2^Z.log2_up (Z.log2_up ?y), H' : ?y <= 2^2^?z |- context[_ mod 2^2^?z] ]
                           => rewrite H' in H
                         end
                       | progress Z.rewrite_mod_small
                       | progress match goal with
                                  | [ H : context[?x mod _] |- _ ]
                                    => revert H; progress Z.rewrite_mod_small; intro
                                  end ].
  Admitted.
End with_round_up.
