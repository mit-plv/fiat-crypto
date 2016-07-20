Require Import Zpower ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import List.
Require Import VerdiTactics.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.

Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Local Open Scope Z_scope.

Section LengthProofs.
  Context `{prm :PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma length_encode {x} : length (encode x) = length limb_widths.
  Proof.
    cbv [encode encodeZ]; intros.
    rewrite encode'_spec;
      auto using encode'_length, limb_widths_nonneg, Nat.eq_le_incl, base_from_limb_widths_length.
  Qed.

  Lemma length_reduce : forall us,
      (length limb_widths <= length us <= length (ext_base limb_widths))%nat ->
      (length (reduce us) = length limb_widths)%nat.
  Proof.
    rewrite extended_base_length.
    unfold reduce; intros.
    rewrite add_length_exact.
    pose proof (@base_from_limb_widths_length limb_widths).
    rewrite map_length, firstn_length, skipn_length, Min.min_l, Max.max_l;
      omega.
  Qed.

  Lemma length_mul {u v} :
      length u = length limb_widths
      -> length v = length limb_widths
      -> length (mul u v) = length limb_widths.
  Proof.
    cbv [mul]; intros.
    apply length_reduce.
    destruct u; try congruence.
    + rewrite @nil_length0 in *; omega.
    + rewrite mul_length_exact, extended_base_length, base_from_limb_widths_length; try omega.
      congruence.
  Qed.

  Section Sub.
  Context {mm : list Z} (mm_length : length mm = length limb_widths).

  Lemma length_sub {u v} :
      length u = length limb_widths
      -> length v = length limb_widths
      -> length (sub mm u v) = length limb_widths.
  Proof.
    cbv [sub]; intros.
    rewrite sub_length, add_length_exact.
    repeat rewrite Max.max_r; omega.
  Qed.
  End Sub.

  Lemma length_carry_and_reduce {us}: forall i, length (carry_and_reduce i us) = length us.
  Proof. intros; unfold carry_and_reduce; autorewrite with distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_and_reduce : distr_length.

  Lemma length_carry {u i} :
    length u = length limb_widths
    -> length (carry i u) = length limb_widths.
  Proof. intros; unfold carry; break_if; autorewrite with distr_length; omega. Qed.
  Hint Rewrite @length_carry : distr_length.

  Lemma length_modulus_digits : length modulus_digits = length limb_widths.
  Proof.
    intros; unfold modulus_digits, encodeZ.
    rewrite encode'_spec, encode'_length;
      auto using encode'_length, limb_widths_nonneg, Nat.eq_le_incl, base_from_limb_widths_length.
  Qed.

  Lemma length_conditional_subtract_modulus {u cond} :
    length u = length limb_widths
    -> length (conditional_subtract_modulus u cond) = length limb_widths.
  Proof.
    intros; unfold conditional_subtract_modulus.
    rewrite map2_length, map_length, length_modulus_digits.
    apply Min.min_case; omega.
  Qed.

End LengthProofs.