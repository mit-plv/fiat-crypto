Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Coq.NArith.NArith.
Require Import Crypto.Util.NatUtil Crypto.Util.Decidable.
Require Export Crypto.Util.NUtil.WithoutReferenceToZ.
Require bbv.WordScope.
Require Import bbv.NatLib.
Require Crypto.Util.WordUtil.
Require Import Crypto.Util.ZUtil.Z2Nat.
Require Import Crypto.Util.ZUtil.Shift.

Module N.

#[global]
  Hint Rewrite
    N.succ_double_spec
    N.add_1_r
    Nat2N.inj_succ
    Nat2N.inj_mul
    N2Nat.id: N_nat_conv
 .

  Lemma succ_double_to_nat : forall n,
    N.succ_double n = N.of_nat (S (2 * N.to_nat n)).
  Proof.
    intros.
    replace 2 with (N.to_nat 2) by auto.
    autorewrite with N_nat_conv.
    reflexivity.
  Qed.

  Lemma double_to_nat : forall n,
    N.double n = N.of_nat (2 * N.to_nat n).
  Proof.
    intros.
    replace 2 with (N.to_nat 2) by auto.
    autorewrite with N_nat_conv.
    reflexivity.
  Qed.

  Section ZN.
    Import Coq.ZArith.ZArith.
    Lemma ZToN_NPow2_lt : forall z n, (0 <= z < 2 ^ Z.of_nat n)%Z ->
                                      (Z.to_N z < Npow2 n)%N.
    Proof.
      intros.
      apply WordUtil.bound_check_nat_N.
      apply Znat.Nat2Z.inj_lt.
      rewrite Znat.Z2Nat.id by lia.
      rewrite Z.pow_Zpow.
      replace (Z.of_nat 2) with 2%Z by reflexivity.
      lia.
    Qed.

    Let ZNWord sz x := Word.NToWord sz (BinInt.Z.to_N x).
    Lemma combine_ZNWord : forall sz1 sz2 z1 z2,
        (0 <= Z.of_nat sz1)%Z ->
        (0 <= Z.of_nat sz2)%Z ->
        (0 <= z1 < 2 ^ (Z.of_nat sz1))%Z ->
        (0 <= z2 < 2 ^ (Z.of_nat sz2))%Z ->
        Word.combine (ZNWord sz1 z1) (ZNWord sz2 z2) =
        ZNWord (sz1 + sz2) (Z.lor z1 (Z.shiftl z2 (Z.of_nat sz1))).
    Proof using Type.
      cbv [ZNWord]; intros.
      rewrite !Word.NToWord_nat.
      match goal with |- ?a = _ => rewrite <- (Word.natToWord_wordToNat a) end.
      rewrite WordUtil.wordToNat_combine.
      rewrite !Word.wordToNat_natToWord_idempotent by (rewrite Nnat.N2Nat.id; auto using ZToN_NPow2_lt).
      f_equal.
      rewrite Z.lor_shiftl by auto.
      rewrite !Z_N_nat.
      rewrite Znat.Z2Nat.inj_add by (try apply Z.shiftl_nonneg; lia).
      f_equal.
      rewrite Z.shiftl_mul_pow2 by auto.
      rewrite Znat.Z2Nat.inj_mul by lia.
      rewrite <-Z.pow_Z2N_Zpow by lia.
      rewrite Nat.mul_comm.
      f_equal.
    Qed.
  End ZN.

End N.
#[global]
Hint Rewrite
     N.succ_double_spec
     N.add_1_r
     Nat2N.inj_succ
     Nat2N.inj_mul
     N2Nat.id: N_nat_conv
.
