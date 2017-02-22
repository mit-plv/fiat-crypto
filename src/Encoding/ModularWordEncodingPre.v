Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Bedrock.Word.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil Crypto.Util.WordUtil.
Require Import Crypto.Spec.Encoding.

Local Open Scope nat_scope.

Section ModularWordEncodingPre.
  Context {m : positive} {sz : nat} {m_pos : (0 < m)%Z} {bound_check : Z.to_nat m < 2 ^ sz}.

  Let Fm_enc (x : F m) : word sz := NToWord sz (Z.to_N (F.to_Z x)).

  Let Fm_dec (x_ : word sz) : option (F m) :=
    let z := Z.of_N (wordToN (x_)) in
    if Z_lt_dec z m
      then Some (F.of_Z m z)
      else None
  .

  Lemma Fm_encoding_valid : forall x, Fm_dec (Fm_enc x) = Some x.
  Proof.
    unfold Fm_dec, Fm_enc; intros.
    pose proof (F.to_Z_range x m_pos).
    rewrite wordToN_NToWord_idempotent by (apply bound_check_nat_N;
     assert (Z.to_nat (F.to_Z x) < Z.to_nat m) by (apply Z2Nat.inj_lt; omega); omega).
    rewrite Z2N.id by omega.
    rewrite F.of_Z_to_Z.
    break_if; auto; omega.
  Qed.

  Lemma Fm_encoding_canonical : forall w x, Fm_dec w = Some x -> Fm_enc x = w.
  Proof.
    unfold Fm_dec, Fm_enc; intros ? ? dec_Some.
    break_if; [ | congruence ].
    inversion dec_Some.
    rewrite F.to_Z_of_Z.
    rewrite Z.mod_small by (pose proof (N2Z.is_nonneg (wordToN w)); try omega).
    rewrite N2Z.id.
    apply NToWord_wordToN.
  Qed.

End ModularWordEncodingPre.
