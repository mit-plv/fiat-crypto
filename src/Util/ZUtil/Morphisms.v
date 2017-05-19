(** * [Proper] morphisms for ℤ constants *)
Require Import Coq.omega.Omega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Crypto.Util.ZUtil.Definitions.
Local Open Scope Z_scope.

Module Z.
  (** We prove a bunch of [Proper] lemmas, but do not make them
      instances; making them instances would slow typeclass search
      unacceptably.  In files where we use these, we add them with
      [Local Existing Instances]. *)
  Lemma add_le_Proper : Proper (Z.le ==> Z.le ==> Z.le) Z.add.
  Proof. repeat (omega || intro). Qed.
  Lemma sub_le_ge_Proper : Proper (Z.le ==> Z.ge ==> Z.le) Z.sub.
  Proof. repeat (omega || intro). Qed.
  Lemma sub_le_flip_le_Proper : Proper (Z.le ==> Basics.flip Z.le ==> Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (omega || intro). Qed.
  Lemma sub_le_eq_Proper : Proper (Z.le ==> Logic.eq ==> Z.le) Z.sub.
  Proof. repeat (omega || intro). Qed.
  Lemma log2_up_le_Proper : Proper (Z.le ==> Z.le) Z.log2_up.
  Proof. intros ???; apply Z.log2_up_le_mono; assumption. Qed.
  Lemma log2_le_Proper : Proper (Z.le ==> Z.le) Z.log2.
  Proof. intros ???; apply Z.log2_le_mono; assumption. Qed.
  Lemma pow_Zpos_le_Proper x : Proper (Z.le ==> Z.le) (Z.pow (Z.pos x)).
  Proof. intros ???; apply Z.pow_le_mono_r; try reflexivity; try assumption. Qed.
  Lemma lt_le_flip_Proper_flip_impl
    : Proper (Z.le ==> Basics.flip Z.le ==> Basics.flip Basics.impl) Z.lt.
  Proof. unfold Basics.flip; repeat (omega || intro). Qed.
  Lemma le_Proper_ge_le_flip_impl : Proper (Z.le ==> Z.ge ==> Basics.flip Basics.impl) Z.le.
  Proof. intros ???????; omega. Qed.
  Lemma add_le_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.le ==> Basics.flip Z.le) Z.add.
  Proof. unfold Basics.flip; repeat (omega || intro). Qed.
  Lemma sub_le_ge_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.ge ==> Basics.flip Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (omega || intro). Qed.
  Lemma sub_flip_le_le_Proper_flip : Proper (Basics.flip Z.le ==> Z.le ==> Basics.flip Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (omega || intro). Qed.
  Lemma sub_le_eq_Proper_flip : Proper (Basics.flip Z.le ==> Logic.eq ==> Basics.flip Z.le) Z.sub.
  Proof. unfold Basics.flip; repeat (omega || intro). Qed.
  Lemma log2_up_le_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.le) Z.log2_up.
  Proof. intros ???; apply Z.log2_up_le_mono; assumption. Qed.
  Lemma log2_le_Proper_flip : Proper (Basics.flip Z.le ==> Basics.flip Z.le) Z.log2.
  Proof. intros ???; apply Z.log2_le_mono; assumption. Qed.
  Lemma pow_Zpos_le_Proper_flip x : Proper (Basics.flip Z.le ==> Basics.flip Z.le) (Z.pow (Z.pos x)).
  Proof. intros ???; apply Z.pow_le_mono_r; try reflexivity; try assumption. Qed.
  Lemma add_with_carry_le_Proper : Proper (Z.le ==> Z.le ==> Z.le ==> Z.le) Z.add_with_carry.
  Proof. unfold Z.add_with_carry; repeat (omega || intro). Qed.
  Lemma sub_with_borrow_le_Proper : Proper (Basics.flip Z.le ==> Z.le ==> Basics.flip Z.le ==> Z.le) Z.sub_with_borrow.
  Proof. unfold Z.sub_with_borrow, Z.add_with_carry, Basics.flip; repeat (omega || intro). Qed.
End Z.
