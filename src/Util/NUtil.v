Require Import Coq.NArith.NArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Util.NatUtil Crypto.Util.Decidable.
Require Bedrock.Word.
Require Crypto.Util.WordUtil.

Module N.
  Lemma size_le a b : (a <= b -> N.size a <= N.size b)%N.
  Proof.
    destruct (dec (a=0)%N), (dec (b=0)%N); subst; auto using N.le_0_l.
    { destruct a; auto. }
    { rewrite !N.size_log2 by assumption.
      rewrite <-N.succ_le_mono.
      apply N.log2_le_mono. }
  Qed.

  Lemma le_to_nat a b : (a <= b)%N <-> (N.to_nat a <= N.to_nat b)%nat.
  Proof.
    rewrite <-N.lt_succ_r.
    rewrite <-Nat.lt_succ_r.
    rewrite <-Nnat.N2Nat.inj_succ.
    rewrite <-NatUtil.Nat2N_inj_lt.
    rewrite !Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Lemma size_nat_equiv : forall n, N.size_nat n = N.to_nat (N.size n).
  Proof.
    destruct n as [|p]; auto; simpl; induction p as [p IHp|p IHp|]; simpl; auto; rewrite IHp, Pnat.Pos2Nat.inj_succ; reflexivity.
  Qed.

  Lemma size_nat_le a b : (a <= b)%N -> (N.size_nat a <= N.size_nat b)%nat.
  Proof.
    rewrite !size_nat_equiv.
    rewrite <-le_to_nat.
    apply size_le.
  Qed.

  Lemma shiftr_size : forall n bound, N.size_nat n <= bound ->
    N.shiftr_nat n bound = 0%N.
  Proof.
    intros n bound H.
    rewrite <- (Nat2N.id bound).
    rewrite Nshiftr_nat_equiv.
    destruct (N.eq_dec n 0); subst; [apply N.shiftr_0_l|].
    apply N.shiftr_eq_0.
    rewrite size_nat_equiv in *.
    rewrite N.size_log2 in * by auto.
    apply N.le_succ_l.
    rewrite <- N.compare_le_iff.
    rewrite N2Nat.inj_compare.
    rewrite <- Compare_dec.nat_compare_le.
    rewrite Nat2N.id.
    auto.
  Qed.

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

  Lemma shiftr_succ : forall n i,
    N.to_nat (N.shiftr_nat n i) =
    if N.testbit_nat n i
    then S (2 * N.to_nat (N.shiftr_nat n (S i)))
    else (2 * N.to_nat (N.shiftr_nat n (S i))).
  Proof.
    intros n i.
    rewrite Nshiftr_nat_S.
    case_eq (N.testbit_nat n i); intro testbit_i;
      pose proof (Nshiftr_nat_spec n i 0) as shiftr_n_odd;
      rewrite Nbit0_correct in shiftr_n_odd; simpl in shiftr_n_odd;
      rewrite testbit_i in shiftr_n_odd.
    + pose proof (Ndiv2_double_plus_one (N.shiftr_nat n i) shiftr_n_odd) as Nsucc_double_shift.
      rewrite succ_double_to_nat in Nsucc_double_shift.
      apply Nat2N.inj.
      rewrite Nsucc_double_shift.
      apply N2Nat.id.
    + pose proof (Ndiv2_double (N.shiftr_nat n i) shiftr_n_odd) as Nsucc_double_shift.
      rewrite double_to_nat in Nsucc_double_shift.
      apply Nat2N.inj.
      rewrite Nsucc_double_shift.
      apply N2Nat.id.
  Qed.

  Section ZN.
    Import Coq.ZArith.ZArith.
    Lemma ZToN_NPow2_lt : forall z n, (0 <= z < 2 ^ Z.of_nat n)%Z ->
                                      (Z.to_N z < Word.Npow2 n)%N.
    Proof.
      intros.
      apply WordUtil.bound_check_nat_N.
      apply Znat.Nat2Z.inj_lt.
      rewrite Znat.Z2Nat.id by omega.
      rewrite ZUtil.Z.pow_Zpow.
      replace (Z.of_nat 2) with 2%Z by reflexivity.
      omega.
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
      rewrite ZUtil.Z.lor_shiftl by auto.
      rewrite !Z_N_nat.
      rewrite Znat.Z2Nat.inj_add by (try apply Z.shiftl_nonneg; omega).
      f_equal.
      rewrite Z.shiftl_mul_pow2 by auto.
      rewrite Znat.Z2Nat.inj_mul by omega.
      rewrite <-ZUtil.Z.pow_Z2N_Zpow by omega.
      rewrite Nat.mul_comm.
      f_equal.
    Qed.
  End ZN.

End N.
