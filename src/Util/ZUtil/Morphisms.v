(** * [Proper] morphisms for ℤ constants *)
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.LandLorBounds.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  (** We prove a bunch of [Proper] lemmas, but do not make them
      instances; making them instances would slow typeclass search
      unacceptably.  In files where we use these, we add them with
      [Local Existing Instances]. *)
  Lemma succ_le_Proper : Proper (Z.le ==> Z.le) Z.succ.
  Proof. repeat (lia || intro). Qed.
  Hint Resolve succ_le_Proper : zarith.
  Lemma add_le_Proper : Proper (Z.le ==> Z.le ==> Z.le) Z.add.
  Proof. repeat (lia || intro). Qed.
  Hint Resolve add_le_Proper : zarith.
  Lemma add_le_Proper' x : Proper (Z.le ==> Z.le) (Z.add x).
  Proof. repeat (lia || intro). Qed.
  Hint Resolve add_le_Proper' : zarith.
  Lemma sub_le_ge_Proper : Proper (Z.le ==> Z.ge ==> Z.le) Z.sub.
  Proof. repeat (lia || intro). Qed.
  Hint Resolve sub_le_ge_Proper : zarith.
  Lemma sub_le_flip_le_Proper : Proper (Z.le ==> Basics.flip Z.le ==> Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_le_flip_le_Proper : zarith.
  Lemma sub_le_eq_Proper : Proper (Z.le ==> Logic.eq ==> Z.le) Z.sub.
  Proof. repeat (lia || intro). Qed.
  Hint Resolve sub_le_eq_Proper : zarith.
  Lemma mul_Zpos_le_Proper p : Proper (Z.le ==> Z.le) (Z.mul (Z.pos p)).
  Proof. repeat (nia || intro). Qed.
  Hint Resolve mul_Zpos_le_Proper : zarith.
  Lemma log2_up_le_Proper : Proper (Z.le ==> Z.le) Z.log2_up.
  Proof. intros ???; apply Z.log2_up_le_mono; assumption. Qed.
  Hint Resolve log2_up_le_Proper : zarith.
  Lemma log2_le_Proper : Proper (Z.le ==> Z.le) Z.log2.
  Proof. intros ???; apply Z.log2_le_mono; assumption. Qed.
  Hint Resolve log2_le_Proper : zarith.
  Lemma pow_Zpos_le_Proper x : Proper (Z.le ==> Z.le) (Z.pow (Z.pos x)).
  Proof. intros ???; apply Z.pow_le_mono_r; try reflexivity; try assumption. Qed.
  Hint Resolve pow_Zpos_le_Proper : zarith.
  Lemma lt_le_flip_Proper_flip_impl
    : Proper (Z.le ==> Basics.flip Z.le ==> Basics.flip Basics.impl) Z.lt.
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve lt_le_flip_Proper_flip_impl : zarith.
  Lemma le_Proper_ge_le_flip_impl : Proper (Z.le ==> Z.ge ==> Basics.flip Basics.impl) Z.le.
  Proof. intros ???????; lia. Qed.
  Hint Resolve le_Proper_ge_le_flip_impl : zarith.
  Lemma add_le_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.le ==> Basics.flip Z.le) Z.add.
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve add_le_Proper_flip : zarith.
  Lemma sub_le_ge_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.ge ==> Basics.flip Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_le_ge_Proper_flip : zarith.
  Lemma sub_flip_le_le_Proper_flip : Proper (Basics.flip Z.le ==> Z.le ==> Basics.flip Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_flip_le_le_Proper_flip : zarith.
  Lemma sub_le_eq_Proper_flip : Proper (Basics.flip Z.le ==> Logic.eq ==> Basics.flip Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_le_eq_Proper_flip : zarith.
  Lemma log2_up_le_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.le) Z.log2_up.
  Proof. intros ???; apply Z.log2_up_le_mono; assumption. Qed.
  Hint Resolve log2_up_le_Proper_flip : zarith.
  Lemma log2_le_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.le) Z.log2.
  Proof. intros ???; apply Z.log2_le_mono; assumption. Qed.
  Hint Resolve log2_le_Proper_flip : zarith.
  Lemma pow_Zpos_le_Proper_flip x : Proper (Basics.flip Z.le ==> Basics.flip Z.le) (Z.pow (Z.pos x)).
  Proof. intros ???; apply Z.pow_le_mono_r; try reflexivity; try assumption. Qed.
  Hint Resolve pow_Zpos_le_Proper_flip : zarith.
  Lemma add_with_carry_le_Proper : Proper (Z.le ==> Z.le ==> Z.le ==> Z.le) Z.add_with_carry.
  Proof. unfold Z.add_with_carry; repeat (lia || intro). Qed.
  Hint Resolve add_with_carry_le_Proper : zarith.
  Lemma sub_with_borrow_le_Proper : Proper (Basics.flip Z.le ==> Z.le ==> Basics.flip Z.le ==> Z.le) Z.sub_with_borrow.
  Proof. unfold Z.sub_with_borrow, Z.add_with_carry, Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_with_borrow_le_Proper : zarith.
  Lemma opp_flip_le_le_Proper : Proper (Basics.flip Z.le ==> Z.le) Z.opp.
  Proof. cbv [Basics.flip]; repeat (lia || intro). Qed.
  Hint Resolve opp_flip_le_le_Proper : zarith.
  Lemma opp_le_flip_le_Proper : Proper (Z.le ==> Basics.flip Z.le) Z.opp.
  Proof. cbv [Basics.flip]; repeat (lia || intro). Qed.
  Hint Resolve opp_le_flip_le_Proper : zarith.
  Lemma opp_le_ge_Proper : Proper (Z.le ==> Z.ge) Z.opp.
  Proof. cbv [Basics.flip]; repeat (lia || intro). Qed.
  Hint Resolve opp_le_ge_Proper : zarith.
  Lemma opp_ge_le_Proper : Proper (Z.ge ==> Z.le) Z.opp.
  Proof. cbv [Basics.flip]; repeat (lia || intro). Qed.
  Hint Resolve opp_ge_le_Proper : zarith.
  Lemma add_le_Proper'' x : Proper (Z.le ==> Z.le) (fun y => Z.add y x).
  Proof. repeat (lia || intro). Qed.
  Hint Resolve add_le_Proper'' : zarith.
  Lemma sub_le_ge_Proper_r p : Proper (Z.le ==> Z.ge) (Z.sub p).
  Proof. repeat (lia || intro). Qed.
  Hint Resolve sub_le_ge_Proper_r : zarith.
  Lemma sub_le_le_Proper_l p : Proper (Z.le ==> Z.le) (fun x => Z.sub x p).
  Proof. repeat (lia || intro). Qed.
  Hint Resolve sub_le_le_Proper_l : zarith.
  Lemma sub_le_flip_le_Proper_r p : Proper (Z.le ==> Basics.flip Z.le) (Z.sub p).
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_le_flip_le_Proper_r : zarith.
  Lemma sub_flip_le_le_Proper_r p : Proper (Basics.flip Z.le ==> Z.le) (Z.sub p).
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_flip_le_le_Proper_r : zarith.
  Lemma sub_ge_le_Proper_r p : Proper (Z.ge ==> Z.le) (Z.sub p).
  Proof. unfold Basics.flip; repeat (lia || intro). Qed.
  Hint Resolve sub_ge_le_Proper_r : zarith.
  Lemma mul_Z0_le_Proper : Proper (Z.le ==> Z.le) (Z.mul Z0).
  Proof. repeat (nia || intro). Qed.
  Hint Resolve mul_Z0_le_Proper : zarith.
  Lemma mul_Zneg_le_flip_le_Proper p : Proper (Z.le ==> Basics.flip Z.le) (Z.mul (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_le_flip_le_Proper : zarith.
  Lemma mul_Zneg_le_ge_Proper p : Proper (Z.le ==> Z.ge) (Z.mul (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_le_ge_Proper : zarith.
  Lemma mul_Zneg_flip_le_le_Proper p : Proper (Basics.flip Z.le ==> Z.le) (Z.mul (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_flip_le_le_Proper : zarith.
  Lemma mul_Zneg_ge_le_Proper p : Proper (Z.ge ==> Z.le) (Z.mul (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_ge_le_Proper : zarith.
  Lemma mul_Zpos_le_Proper' p : Proper (Z.le ==> Z.le) (fun y => Z.mul y (Zpos p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zpos_le_Proper' : zarith.
  Lemma mul_Z0_le_Proper' : Proper (Z.le ==> Z.le) (fun y => Z.mul y Z0).
  Proof. repeat (nia || intro). Qed.
  Hint Resolve mul_Z0_le_Proper' : zarith.
  Lemma mul_Zneg_le_flip_le_Proper' p : Proper (Z.le ==> Basics.flip Z.le) (fun y => Z.mul y (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_le_flip_le_Proper' : zarith.
  Lemma mul_Zneg_le_ge_Proper' p : Proper (Z.le ==> Z.ge) (fun y => Z.mul y (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_le_ge_Proper' : zarith.
  Lemma mul_Zneg_flip_le_le_Proper' p : Proper (Basics.flip Z.le ==> Z.le) (fun y => Z.mul y (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_flip_le_le_Proper' : zarith.
  Lemma mul_Zneg_ge_le_Proper' p : Proper (Z.ge ==> Z.le) (fun y => Z.mul y (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || intro). Qed.
  Hint Resolve mul_Zneg_ge_le_Proper' : zarith.
  Lemma div_Zpos_le_Proper_r p : Proper (Z.le ==> Z.le) (fun x => Z.div x (Zpos p)).
  Proof. repeat (nia || Z.div_mod_to_quot_rem || intro). Qed.
  Hint Resolve div_Zpos_le_Proper_r : zarith.
  Lemma div_Z0_le_Proper_r : Proper (Z.le ==> Z.le) (fun x => Z.div x Z0).
  Proof. repeat (nia || Z.div_mod_to_quot_rem || intro). Qed.
  Hint Resolve div_Z0_le_Proper_r : zarith.
  Lemma div_Zneg_le_flip_le_Proper_r p : Proper (Z.le ==> Basics.flip Z.le) (fun x => Z.div x (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || Z.div_mod_to_quot_rem || intro). Qed.
  Hint Resolve div_Zneg_le_flip_le_Proper_r : zarith.
  Lemma div_Zneg_flip_le_le_Proper_r p : Proper (Basics.flip Z.le ==> Z.le) (fun x => Z.div x (Zneg p)).
  Proof. cbv [Basics.flip]; repeat (nia || Z.div_mod_to_quot_rem || intro). Qed.
  Hint Resolve div_Zneg_flip_le_le_Proper_r : zarith.
  Lemma div_Z0_le_Proper_l : Proper (Z.le ==> Z.le) (Z.div Z0).
  Proof. do 3 intro; destruct_head' Z; cbv; congruence. Qed.
  Hint Resolve div_Z0_le_Proper_l : zarith.
  Local Ltac div_Proper_t :=
    let H := fresh in
    cbv [Basics.flip]; intros ?? H; apply Pos2Z.pos_le_pos in H;
    apply Z.div_cross_le_abs; cbn [Z.sgn Z.abs]; try nia.
  Lemma div_Zpos_Zpos_le_Proper_l p : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.div (Zpos p) (Zpos x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zpos_Zpos_le_Proper_l : zarith.
  Lemma div_Zpos_Zneg_le_Proper_l p : Proper (Pos.le ==> Z.le) (fun x => Z.div (Zpos p) (Zneg x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zpos_Zneg_le_Proper_l : zarith.
  Lemma div_Zneg_Zpos_le_Proper_l p : Proper (Pos.le ==> Z.le) (fun x => Z.div (Zneg p) (Zpos x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zneg_Zpos_le_Proper_l : zarith.
  Lemma div_Zneg_Zneg_le_Proper_l p : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.div (Zneg p) (Zneg x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zneg_Zneg_le_Proper_l : zarith.
  Lemma div_Z0_Zpos_le_Proper_l : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.div Z0 (Zpos x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Z0_Zpos_le_Proper_l : zarith.
  Lemma div_Z0_Zneg_le_Proper_l : Proper (Pos.le ==> Z.le) (fun x => Z.div Z0 (Zneg x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Z0_Zneg_le_Proper_l : zarith.
  Lemma div_Zpos_Zpos_le_Proper_r x : Proper (Pos.le ==> Z.le) (fun p => Z.div (Zpos p) (Zpos x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zpos_Zpos_le_Proper_r : zarith.
  Lemma div_Zpos_Zneg_le_Proper_r x : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.div (Zpos p) (Zneg x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zpos_Zneg_le_Proper_r : zarith.
  Lemma div_Zneg_Zpos_le_Proper_r x : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.div (Zneg p) (Zpos x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zneg_Zpos_le_Proper_r : zarith.
  Lemma div_Zneg_Zneg_le_Proper_r x : Proper (Pos.le ==> Z.le) (fun p => Z.div (Zneg p) (Zneg x)).
  Proof. div_Proper_t. Qed.
  Hint Resolve div_Zneg_Zneg_le_Proper_r : zarith.
  Lemma div_Zpos_Z0_le_Proper_r : Proper (Pos.le ==> Z.le) (fun p => Z.div (Zpos p) Z0).
  Proof. do 3 intro; cbv; congruence. Qed.
  Hint Resolve div_Zpos_Z0_le_Proper_r : zarith.
  Lemma div_Zneg_Z0_le_Proper_r : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.div (Zneg p) Z0).
  Proof. do 3 intro; cbv; congruence. Qed.
  Hint Resolve div_Zneg_Z0_le_Proper_r : zarith.
  Local Ltac shift_t :=
    repeat first [ progress intros
                 | progress cbv [Proper respectful Basics.flip] in *
                 | progress rewrite ?Z.shiftr_div_pow2, ?Z.shiftr_mul_pow2, ?Z.shiftl_div_pow2, ?Z.shiftl_mul_pow2, ?Z.div_1_r, ?Zdiv_0_l by lia
                 | progress (cbn [Z.pow Z.opp]; change Z.pow_pos with (fun x p => Z.pow x (Zpos p)); cbn beta)
                 | progress Z.peel_le
                 | nia
                 | match goal with
                   | [ |- context[(2^Zpos ?p)%Z] ] => unique assert (0 < 2^Zpos p)%Z by (apply Z.pow_pos_nonneg; lia)
                   | [ |- (?x / ?a <= ?x * ?b)%Z ] => transitivity x
                   | [ |- (?x * ?a <= ?x / ?b)%Z ] => transitivity x
                   | [ H : (0 > Z.neg _)%Z |- _ ] => clear H
                   | [ H : (Zneg ?a <= Zneg ?b)%Z |- _ ] => assert ((Zpos b <= Zpos a)%Z) by lia; clear H
                   | [ H : (?a <= ?b)%Z |- context[(2^?a)%Z] ]
                     => unique assert (2^a <= 2^b)%Z by (apply Z.pow_le_mono_r; lia); clear H
                   | [ |- context[(2^Zpos ?a)%Z] ] => generalize dependent (2^Zpos a)%Z; clear a
                   end
                 | progress destruct_head' Z
                 | Z.div_mod_to_quot_rem; nia
                 | apply Z.div_cross_le_abs; cbn [Z.sgn Z.abs]; nia ].
  Lemma shiftr_le_Proper_l : forall y : Z, Proper (Z.le ==> Z.le) (fun x : Z => Z.shiftr x y).
  Proof. shift_t. Qed.
  Hint Resolve shiftr_le_Proper_l : zarith.
  Lemma shiftl_le_Proper_l : forall y : Z, Proper (Z.le ==> Z.le) (fun x : Z => Z.shiftl x y).
  Proof. shift_t. Qed.
  Hint Resolve shiftl_le_Proper_l : zarith.
  Lemma shiftr_le_Proper_r x
        (R := fun b : bool => if b then Basics.flip Z.le else Z.le)
    : Proper (R (0 <=? x)%Z ==> Z.le) (Z.shiftr x).
  Proof. subst R; cbv beta; break_match; Z.ltb_to_lt; shift_t. Qed.
  Hint Resolve shiftr_le_Proper_r : zarith.
  Lemma shiftl_le_Proper_r x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (0 <=? x)%Z ==> Z.le) (Z.shiftl x).
  Proof. subst R; cbv beta; break_match; Z.ltb_to_lt; shift_t. Qed.
  Hint Resolve shiftl_le_Proper_r : zarith.
  Local Ltac shift_Proper_t' :=
    let H := fresh in
    cbv [Basics.flip]; intros ?? H; apply Pos2Z.pos_le_pos in H;
    try ((apply shiftr_le_Proper_r + apply shiftr_le_Proper_l + apply shiftl_le_Proper_r + apply shiftl_le_Proper_l);
         cbv [Z.leb Z.compare Basics.flip];
         lia).
  Lemma shiftr_Zpos_Zpos_le_Proper_l p : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.shiftr (Zpos p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zpos_Zpos_le_Proper_l : zarith.
  Lemma shiftr_Zpos_Zneg_le_Proper_l p : Proper (Pos.le ==> Z.le) (fun x => Z.shiftr (Zpos p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zpos_Zneg_le_Proper_l : zarith.
  Lemma shiftr_Zneg_Zpos_le_Proper_l p : Proper (Pos.le ==> Z.le) (fun x => Z.shiftr (Zneg p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zneg_Zpos_le_Proper_l : zarith.
  Lemma shiftr_Zneg_Zneg_le_Proper_l p : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.shiftr (Zneg p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zneg_Zneg_le_Proper_l : zarith.
  Lemma shiftr_Z0_Zpos_le_Proper_l : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.shiftr Z0 (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Z0_Zpos_le_Proper_l : zarith.
  Lemma shiftr_Z0_Zneg_le_Proper_l : Proper (Pos.le ==> Z.le) (fun x => Z.shiftr Z0 (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Z0_Zneg_le_Proper_l : zarith.
  Lemma shiftr_Zpos_Zpos_le_Proper_r x : Proper (Pos.le ==> Z.le) (fun p => Z.shiftr (Zpos p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zpos_Zpos_le_Proper_r : zarith.
  Lemma shiftr_Zpos_Zneg_le_Proper_r x : Proper (Pos.le ==> Z.le) (fun p => Z.shiftr (Zpos p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zpos_Zneg_le_Proper_r : zarith.
  Lemma shiftr_Zneg_Zpos_le_Proper_r x : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.shiftr (Zneg p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zneg_Zpos_le_Proper_r : zarith.
  Lemma shiftr_Zneg_Zneg_le_Proper_r x : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.shiftr (Zneg p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zneg_Zneg_le_Proper_r : zarith.
  Lemma shiftr_Zpos_Z0_le_Proper_r : Proper (Pos.le ==> Z.le) (fun p => Z.shiftr (Zpos p) Z0).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zpos_Z0_le_Proper_r : zarith.
  Lemma shiftr_Zneg_Z0_le_Proper_r : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.shiftr (Zneg p) Z0).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftr_Zneg_Z0_le_Proper_r : zarith.
  Lemma shiftl_Zpos_Zpos_le_Proper_l p : Proper (Pos.le ==> Z.le) (fun x => Z.shiftl (Zpos p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zpos_Zpos_le_Proper_l : zarith.
  Lemma shiftl_Zpos_Zneg_le_Proper_l p : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.shiftl (Zpos p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zpos_Zneg_le_Proper_l : zarith.
  Lemma shiftl_Zneg_Zpos_le_Proper_l p : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.shiftl (Zneg p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zneg_Zpos_le_Proper_l : zarith.
  Lemma shiftl_Zneg_Zneg_le_Proper_l p : Proper (Pos.le ==> Z.le) (fun x => Z.shiftl (Zneg p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zneg_Zneg_le_Proper_l : zarith.
  Lemma shiftl_Z0_Zpos_le_Proper_l : Proper (Pos.le ==> Z.le) (fun x => Z.shiftl Z0 (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Z0_Zpos_le_Proper_l : zarith.
  Lemma shiftl_Z0_Zneg_le_Proper_l : Proper (Basics.flip Pos.le ==> Z.le) (fun x => Z.shiftl Z0 (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Z0_Zneg_le_Proper_l : zarith.
  Lemma shiftl_Zpos_Zpos_le_Proper_r x : Proper (Pos.le ==> Z.le) (fun p => Z.shiftl (Zpos p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zpos_Zpos_le_Proper_r : zarith.
  Lemma shiftl_Zpos_Zneg_le_Proper_r x : Proper (Pos.le ==> Z.le) (fun p => Z.shiftl (Zpos p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zpos_Zneg_le_Proper_r : zarith.
  Lemma shiftl_Zneg_Zpos_le_Proper_r x : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.shiftl (Zneg p) (Zpos x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zneg_Zpos_le_Proper_r : zarith.
  Lemma shiftl_Zneg_Zneg_le_Proper_r x : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.shiftl (Zneg p) (Zneg x)).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zneg_Zneg_le_Proper_r : zarith.
  Lemma shiftl_Zpos_Z0_le_Proper_r : Proper (Pos.le ==> Z.le) (fun p => Z.shiftl (Zpos p) Z0).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zpos_Z0_le_Proper_r : zarith.
  Lemma shiftl_Zneg_Z0_le_Proper_r : Proper (Basics.flip Pos.le ==> Z.le) (fun p => Z.shiftl (Zneg p) Z0).
  Proof. shift_Proper_t'. Qed.
  Hint Resolve shiftl_Zneg_Z0_le_Proper_r : zarith.

  Hint Resolve Z.land_round_Proper_pos_r : zarith.
  Hint Resolve Z.land_round_Proper_pos_l : zarith.
  Hint Resolve Z.lor_round_Proper_pos_r : zarith.
  Hint Resolve Z.lor_round_Proper_pos_l : zarith.
  Hint Resolve Z.land_round_Proper_neg_r : zarith.
  Hint Resolve Z.land_round_Proper_neg_l : zarith.
  Hint Resolve Z.lor_round_Proper_neg_r : zarith.
  Hint Resolve Z.lor_round_Proper_neg_l : zarith.
End Z.
