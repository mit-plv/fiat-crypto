Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Import Bug5107WorkAround.
Import BoundedRewriteNotations.

Local Open Scope Z_scope.

Lemma decode_is_spread_left_immediate_iff
      {n W}
      {decode : decoder n W}
      {sprl : spread_left_immediate W}
      {isdecode : is_decode decode}
  : is_spread_left_immediate sprl
    <-> (forall r count,
            0 <= count < n
            -> tuple_decoder (sprl r count) = decode r << count).
Proof.
  rewrite is_spread_left_immediate_alt by assumption.
  split; intros H r count Hc; specialize (H r count Hc); revert H;
    pose proof (decode_range r);
    assert (0 < 2^count < 2^n) by auto with zarith;
    autorewrite with simpl_tuple_decoder;
    simpl; intro H'; rewrite H';
      autorewrite with Zshift_to_pow;
      Z.rewrite_mod_small; reflexivity.
Qed.

Global Instance decode_is_spread_left_immediate
       {n W}
       {decode : decoder n W}
       {sprl : spread_left_immediate W}
       {isdecode : is_decode decode}
       {issprl : is_spread_left_immediate sprl}
  : forall r count,
    (0 <= count < n)%bounded_rewrite
    -> tuple_decoder (sprl r count) <~=~> decode r << count
  := proj1 decode_is_spread_left_immediate_iff _.


Section tuple2.
  Section spread_left.
    Context (n : Z) {W}
            {ldi : load_immediate W}
            {shl : shift_left_immediate W}
            {shr : shift_right_immediate W}
            {decode : decoder n W}
            {isdecode : is_decode decode}
            {isldi : is_load_immediate ldi}
            {isshl : is_shift_left_immediate shl}
            {isshr : is_shift_right_immediate shr}.

    Lemma spread_left_from_shift_correct
          r count
          (H : 0 < count < n)
      : (decode (shl r count) + decode (shr r (n - count)) << n = decode r << count mod (2^n*2^n))%Z.
    Proof.
      assert (0 <= count < n) by lia.
      assert (0 <= n - count < n) by lia.
      assert (0 < 2^(n-count)) by auto with zarith.
      assert (2^count < 2^n) by auto with zarith.
      pose proof (decode_range r).
      assert (0 <= decode r * 2 ^ count < 2 ^ n * 2^n) by auto with zarith.
      push_decode; autorewrite with Zshift_to_pow zsimplify.
      replace (decode r / 2^(n-count) * 2^n)%Z with ((decode r / 2^(n-count) * 2^(n-count)) * 2^count)%Z
        by (rewrite <- Z.mul_assoc; autorewrite with pull_Zpow zsimplify; reflexivity).
      rewrite Z.mul_div_eq' by lia.
      autorewrite with push_Zmul zsimplify.
      rewrite <- Z.mul_mod_distr_r_full, Z.add_sub_assoc.
      repeat autorewrite with pull_Zpow zsimplify in *.
      reflexivity.
    Qed.

    Global Instance is_spread_left_from_shift
      : is_spread_left_immediate (sprl_from_shift n).
    Proof.
      apply is_spread_left_immediate_alt.
      intros r count; intros.
      pose proof (decode_range r).
      assert (0 < 2^n) by auto with zarith.
      assert (decode r < 2^n * 2^n) by (generalize dependent (decode r); intros; nia).
      autorewrite with simpl_tuple_decoder.
      destruct (Z_zerop count).
      { subst; autorewrite with Zshift_to_pow zsimplify.
        simpl; push_decode.
        autorewrite with push_Zpow zsimplify.
        reflexivity. }
      simpl.
      rewrite <- spread_left_from_shift_correct by lia.
      autorewrite with zsimplify Zpow_to_shift.
      reflexivity.
    Qed.
  End spread_left.

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
    Lemma spread_left_from_shift_half_correct
          r
      : (decode (shl r half_n) + decode (shr r half_n) * (2^half_n * 2^half_n)
         = (decode r * 2^half_n) mod (2^half_n*2^half_n*2^half_n*2^half_n))%Z.
    Proof.
      destruct (0 <? half_n) eqn:Hn; Z.ltb_to_lt.
      { pose proof (spread_left_from_shift_correct (2*half_n) r half_n) as H.
        specialize_by lia.
        autorewrite with Zshift_to_pow push_Zpow zsimplify in *.
        rewrite !Z.mul_assoc in *.
        simpl in *; rewrite <- H; reflexivity. }
      { pose proof (decode_range r).
        pose proof (decode_range (shr r half_n)).
        pose proof (decode_range (shl r half_n)).
        simpl in *.
        autorewrite with push_Zpow in *.
        destruct (Z_zerop half_n).
        { subst; simpl in *.
          autorewrite with zsimplify.
          nia. }
        assert (half_n < 0) by lia.
        assert (2^half_n = 0) by auto with zarith.
        assert (0 < 0) by nia; omega. }
    Qed.
  End full_from_half.
End tuple2.
