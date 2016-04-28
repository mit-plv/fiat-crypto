Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Bedrock.Word.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.WordUtil.
Require Import Crypto.Spec.Encoding.

Local Open Scope nat_scope.

Section ModularWordEncodingPre.
  Context {m : Z} {sz : nat} {m_pos : (0 < m)%Z} {bound_check : Z.to_nat m < 2 ^ sz}.

  Let Fm_enc (x : F m) : word sz := NToWord sz (Z.to_N (FieldToZ x)).

  Let Fm_dec (x_ : word sz) : option (F m) :=
    let z := Z.of_N (wordToN (x_)) in
    if Z_lt_dec z m
      then Some (ZToField z)
      else None
  .

  (* TODO : move to ZUtil *)
  Lemma bound_check_N : forall x : F m, (Z.to_N x < Npow2 sz)%N.
  Proof.
    intro.
    pose proof (FieldToZ_range x m_pos) as x_range.
    rewrite <- Nnat.N2Nat.id.
    rewrite Npow2_nat.
    replace (Z.to_N x) with (N.of_nat (Z.to_nat x)) by apply Z_nat_N.
    apply (Nat2N_inj_lt _ (pow2 sz)).
    rewrite Zpow_pow2.
    destruct x_range as [x_low x_high].
    apply Z2Nat.inj_lt in x_high; try omega.
    rewrite <- ZUtil.pow_Z2N_Zpow by omega.
    replace (Z.to_nat 2) with 2%nat by auto.
    omega.
  Qed.

  (* TODO: move to WordUtil *)
  Lemma wordToN_NToWord_idempotent : forall sz n, (n < Npow2 sz)%N ->
    wordToN (NToWord sz n) = n.
  Proof.
    intros.
    rewrite wordToN_nat, NToWord_nat.
    rewrite wordToNat_natToWord_idempotent; rewrite Nnat.N2Nat.id; auto.
  Qed.

  (* TODO: move to WordUtil *)
  Lemma NToWord_wordToN : forall sz w, NToWord sz (wordToN w) = w.
  Proof.
    intros.
    rewrite wordToN_nat, NToWord_nat, Nnat.Nat2N.id.
    apply natToWord_wordToNat.
  Qed.

  Lemma Fm_encoding_valid : forall x, Fm_dec (Fm_enc x) = Some x.
  Proof.
    unfold Fm_dec, Fm_enc; intros.
    pose proof (FieldToZ_range x m_pos).
    rewrite wordToN_NToWord_idempotent by apply bound_check_N.
    rewrite Z2N.id by omega.
    rewrite ZToField_idempotent.
    break_if; auto; omega.
  Qed.

  Lemma Fm_encoding_canonical : forall w x, Fm_dec w = Some x -> Fm_enc x = w.
  Proof.
    unfold Fm_dec, Fm_enc; intros ? ? dec_Some.
    break_if; [ | congruence ].
    inversion dec_Some.
    rewrite FieldToZ_ZToField.
    rewrite Z.mod_small by (pose proof (N2Z.is_nonneg (wordToN w)); try omega).
    rewrite N2Z.id.
    apply NToWord_wordToN.
  Qed.

End ModularWordEncodingPre.
