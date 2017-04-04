Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Opaque tuple_decoder.
Local Arguments Z.mul !_ !_.

Section load_immediate.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {ldi : load_immediate W}
          {is_ldi : is_load_immediate ldi}.

  Global Instance is_load_immediate_double
    : is_load_immediate (ldi_double n).
  Proof using Type*.
    intros x H; hnf in H.
    pose proof (decode_exponent_nonnegative decode (ldi x)).
    assert (0 <= x mod 2^n < 2^n) by auto with zarith.
    assert (x / 2^n < 2^n)
      by (apply Z.div_lt_upper_bound; autorewrite with pull_Zpow zsimplify; auto with zarith).
    assert (0 <= x / 2^n < 2^n) by (split; Z.zero_bounds).
    unfold ldi_double, load_immediate_double; simpl.
    autorewrite with simpl_tuple_decoder Zshift_to_pow; simpl; push_decode.
    autorewrite with zsimplify; reflexivity.
  Qed.
End load_immediate.
