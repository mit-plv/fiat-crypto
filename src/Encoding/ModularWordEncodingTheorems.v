Require Import Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Import Bedrock.Word.
Require Import Crypto.Tactics.VerdiTactics Crypto.Util.Tactics.
Require Import Crypto.Spec.Encoding.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Spec.ModularWordEncoding.


Local Open Scope F_scope.

Section SignBit.
  Context {m : Z} {prime_m : prime m} {two_lt_m : (2 < m)%Z} {sz : nat} {bound_check : (Z.to_nat m < 2 ^ sz)%nat}.

  Lemma sign_bit_parity : forall x, @sign_bit m sz x = Z.odd x.
  Proof.
    unfold sign_bit, Fm_enc; intros.
    pose proof (shatter_word (NToWord sz (Z.to_N x))) as shatter.
    case_eq sz; intros; subst; rewrite shatter.
    + pose proof (prime_ge_2 m prime_m).
      simpl in bound_check.
      assert (m < 1)%Z by (apply Z2Nat.inj_lt; try omega; assumption).
      omega.
    + assert (0 < m)%Z as m_pos by (pose proof prime_ge_2 m prime_m; omega).
      pose proof (Zmod.FieldToZ_range x m_pos).
      destruct (FieldToZ x); auto.
      - destruct p; auto.
      - pose proof (Pos2Z.neg_is_neg p); omega.
   Qed.

  Lemma sign_bit_zero : @sign_bit m sz 0 = false.
  Proof.
    rewrite sign_bit_parity; auto.
  Qed.

  Lemma odd_m : Z.odd m = true. Admitted.

  Lemma sign_bit_opp (x : F m) (Hnz:x <> 0) : negb (@sign_bit m sz x) = @sign_bit m sz (opp x).
  Proof.
    pose proof Zmod.FieldToZ_nonzero_range x Hnz; specialize_by omega.
    rewrite !sign_bit_parity, Zmod.FieldToZ_opp, Z_mod_nz_opp_full,
      Zmod_small, Z.odd_sub, odd_m, (Bool.xorb_true_l (Z.odd x)) by
       (omega || rewrite Zmod_small by omega; auto using Zmod.FieldToZ_nonzero); trivial.
  Qed.
End SignBit.
