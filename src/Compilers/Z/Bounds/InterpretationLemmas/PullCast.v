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
    generalize dependent (Bounds.interp_op opc bs); simpl; intros.
    repeat (destruct_one_head flat_type; try solve [ inversion opc ]).
    all:simpl in *; destruct_head unit; destruct_head True; simpl in *.
    all:unfold unzify_op, cast_back_flat_const, lift_op in *; simpl in *.
    all:unfold Bounds.is_bounded_by', ZRange.is_bounded_by' in *.
    all:change (@interpToZ) with (fun t1 => cast_const (t1:=t1) (t2:=TZ)) in *.
    all:cbv beta in *.
    { specialize (H0 (cast_const v)).
      specialize_by_assumption.
      (*{ simpl in *.
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
*)
  Admitted.
End with_round_up.
