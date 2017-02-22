Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section PseudoMersenneBaseParamProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w.
  Proof. auto using Z.lt_le_incl, limb_widths_pos. Qed.

  Lemma k_nonneg : 0 <= k.
  Proof. apply sum_firstn_limb_widths_nonneg, limb_widths_nonneg. Qed.

  Lemma lt_modulus_2k : modulus < 2 ^ k.
  Proof.
    replace (2 ^ k) with (modulus + c) by (unfold c; ring).
    pose proof c_pos; omega.
  Qed. Hint Resolve lt_modulus_2k.

  Lemma modulus_pos : 0 < modulus.
  Proof.
    pose proof (NumTheoryUtil.lt_1_p _ prime_modulus); omega.
  Qed. Hint Resolve modulus_pos.

  Lemma modulus_nonzero : Z.pos modulus <> 0.
    pose proof (Znumtheory.prime_ge_2 _ prime_modulus); omega.
  Qed.

  (* a = r + s(2^k) = r + s(2^k - c + c) = r + s(2^k - c) + cs = r + cs *)
  Lemma pseudomersenne_add: forall x y, (x + ((2^k) * y)) mod modulus = (x + (c * y)) mod modulus.
  Proof.
    intros.
    replace (2^k) with ((2^k - c) + c) by ring.
    rewrite Z.mul_add_distr_r, Zplus_mod.
    unfold c.
    rewrite Z.sub_sub_distr, Z.sub_diag.
    rewrite Z.mul_comm, Z.mod_add_l; auto using modulus_nonzero.
    rewrite <- Zplus_mod; auto.
  Qed.

  Lemma pseudomersenne_add': forall x y0 y1 z, (z - x + ((2^k) * y0 * y1)) mod modulus = (c * y0 * y1 - x + z) mod modulus.
  Proof.
    intros; rewrite <- !Z.add_opp_r, <- !Z.mul_assoc, pseudomersenne_add; apply f_equal2; omega.
  Qed.

  Lemma extended_shiftadd: forall (us : digits),
    decode (ext_base limb_widths) us =
      decode base (firstn (length base) us)
        + (2 ^ k * decode base (skipn (length base) us)).
  Proof.
    intros.
    unfold decode; rewrite <- mul_each_rep.
    rewrite ext_base_alt by apply limb_widths_nonneg.
    fold k; fold (mul_each (2 ^ k) base).
    rewrite base_mul_app.
    rewrite <- mul_each_rep; auto.
  Qed.

  Global Instance bv : BaseSystem.BaseVector base := {
    base_positive := base_positive limb_widths_nonneg;
    b0_1 := fun x => b0_1 x limb_widths_nonnil;
    base_good := base_good limb_widths_nonneg limb_widths_good
  }.

  Lemma nth_default_base_positive : forall i, (i < length base)%nat ->
    nth_default 0 base i > 0.
  Proof.
    intros.
    pose proof (nth_error_length_exists_value _ _ H).
    destruct H0.
    pose proof (nth_error_value_In _ _ _ H0).
    pose proof (BaseSystem.base_positive _ H1).
    unfold nth_default.
    rewrite H0; auto.
  Qed.

  Lemma base_succ_div_mult : forall i, ((S i) < length base)%nat ->
    nth_default 0 base (S i) = nth_default 0 base i *
    (nth_default 0 base (S i) / nth_default 0 base i).
  Proof.
    intros.
    apply Z_div_exact_2; try (apply nth_default_base_positive; omega).
    apply base_succ; distr_length; eauto using limb_widths_nonneg.
  Qed.

End PseudoMersenneBaseParamProofs.
