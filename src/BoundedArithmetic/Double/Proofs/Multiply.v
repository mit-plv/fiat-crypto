Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.SpreadLeftImmediate.
Require Import Crypto.BoundedArithmetic.Double.Proofs.RippleCarryAddSub.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Import Bug5107WorkAround.
Import BoundedRewriteNotations.

Local Open Scope Z_scope.

Local Opaque tuple_decoder.

Lemma decode_mul_double_iff
      {n W}
      {decode : decoder n W}
      {muldw : multiply_double W}
      {isdecode : is_decode decode}
  : is_mul_double muldw
    <-> (forall x y, tuple_decoder (muldw x y) = (decode x * decode y)%Z).
Proof.
  rewrite is_mul_double_alt by assumption.
  split; intros H x y; specialize (H x y); revert H;
    pose proof (decode_range x); pose proof (decode_range y);
      assert (0 <= decode x * decode y < 2^n * 2^n) by nia;
      assert (0 <= n) by eauto using decode_exponent_nonnegative;
      autorewrite with simpl_tuple_decoder;
      simpl; intro H'; rewrite H';
        Z.rewrite_mod_small; reflexivity.
Qed.

Global Instance decode_mul_double
           {n W}
           {decode : decoder n W}
           {muldw : multiply_double W}
           {isdecode : is_decode decode}
           {ismuldw : is_mul_double muldw}
  : forall x y, tuple_decoder (muldw x y) <~=~> (decode x * decode y)%Z
  := proj1 decode_mul_double_iff _.

Section tuple2.
  Local Arguments Z.pow !_ !_.
  Local Arguments Z.mul !_ !_.

  Local Opaque ripple_carry_adc.
  Section full_from_half.
    Context {W}
            {mulhwll : multiply_low_low W}
            {mulhwhl : multiply_high_low W}
            {mulhwhh : multiply_high_high W}
            {adc : add_with_carry W}
            {shl : shift_left_immediate W}
            {shr : shift_right_immediate W}
            {half_n : Z}
            {ldi : load_immediate W}
            {decode : decoder (2 * half_n) W}
            {ismulhwll : is_mul_low_low half_n mulhwll}
            {ismulhwhl : is_mul_high_low half_n mulhwhl}
            {ismulhwhh : is_mul_high_high half_n mulhwhh}
            {isadc : is_add_with_carry adc}
            {isshl : is_shift_left_immediate shl}
            {isshr : is_shift_right_immediate shr}
            {isldi : is_load_immediate ldi}
            {isdecode : is_decode decode}.

    Local Arguments Z.mul !_ !_.

    Lemma decode_mul_double_mod x y
      : (tuple_decoder (mul_double half_n x y) = (decode x * decode y) mod (2^(2 * half_n) * 2^(2*half_n)))%Z.
    Proof.
      assert (0 <= 2 * half_n) by eauto using decode_exponent_nonnegative.
      assert (0 <= half_n) by omega.
      unfold mul_double, Let_In.
      push_decode; autorewrite with simpl_tuple_decoder; simplify_projections.
      autorewrite with zsimplify Zshift_to_pow push_Zpow.
      rewrite !spread_left_from_shift_half_correct.
      push_decode.
      generalize_decode_var.
      simpl in *.
      autorewrite with push_Zpow in *.
      repeat autorewrite with Zshift_to_pow zsimplify push_Zpow.
      rewrite <- !(Z.mul_mod_distr_r_full _ _ (_^_ * _^_)), ?Z.mul_assoc.
      Z.rewrite_mod_small.
      push_Zmod; pull_Zmod.
      apply f_equal2; [ | reflexivity ].
      Z.div_mod_to_quot_rem; nia.
    Qed.

    Lemma decode_mul_double_function x y
      : tuple_decoder (mul_double half_n x y) = (decode x * decode y)%Z.
    Proof.
      rewrite decode_mul_double_mod; generalize_decode_var.
      simpl in *; Z.rewrite_mod_small; reflexivity.
    Qed.

    Global Instance mul_double_is_multiply_double : is_mul_double mul_double_multiply.
    Proof.
      apply decode_mul_double_iff; apply decode_mul_double_function.
    Qed.
  End full_from_half.

  Section half_from_full.
    Context {n W}
            {decode : decoder n W}
            {muldw : multiply_double W}
            {isdecode : is_decode decode}
            {ismuldw : is_mul_double muldw}.

    Local Ltac t :=
      hnf; intros [??] [??];
      assert (0 <= n) by eauto using decode_exponent_nonnegative;
      assert (0 < 2^n) by auto with zarith;
      assert (forall x y, 0 <= x < 2^n -> 0 <= y < 2^n -> 0 <= x * y < 2^n * 2^n) by auto with zarith;
      simpl @Interface.mulhwhh; simpl @Interface.mulhwhl; simpl @Interface.mulhwll;
      rewrite decode_mul_double; autorewrite with simpl_tuple_decoder Zshift_to_pow zsimplify push_Zpow;
      Z.rewrite_mod_small;
      try reflexivity.

    Global Instance mul_double_is_multiply_low_low : is_mul_low_low n mul_double_multiply_low_low.
    Proof. t. Qed.
    Global Instance mul_double_is_multiply_high_low : is_mul_high_low n mul_double_multiply_high_low.
    Proof. t. Qed.
    Global Instance mul_double_is_multiply_high_high : is_mul_high_high n mul_double_multiply_high_high.
    Proof. t. Qed.
  End half_from_full.
End tuple2.
