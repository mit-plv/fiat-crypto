Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.ShiftLeftRightTactic.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.

Local Open Scope Z_scope.

Local Opaque tuple_decoder.
Local Arguments Z.pow !_ !_.
Local Arguments Z.mul !_ !_.

Section shr.
  Context (n : Z) {W}
          {ldi : load_immediate W}
          {shl : shift_left_immediate W}
          {shr : shift_right_immediate W}
          {or : bitwise_or W}
          {decode : decoder n W}
          {isdecode : is_decode decode}
          {isldi : is_load_immediate ldi}
          {isshl : is_shift_left_immediate shl}
          {isshr : is_shift_right_immediate shr}
          {isor : is_bitwise_or or}.

  Global Instance is_shift_right_immediate_double : is_shift_right_immediate (shr_double n).
  Proof.
    intros r count H; hnf in H.
    assert (0 < 2^count) by auto with zarith.
    assert (0 < 2^(n+count)) by auto with zarith.
    assert (forall n', ~n' + count < n -> 2^n <= 2^(n'+count)) by auto with zarith omega.
    assert (forall n', ~n' + count < n -> 2^n <= 2^(n'+count)) by auto with zarith omega.
    unfold shr_double; simpl.
    generalize (decode_range r).
    pose proof (decode_range (fst r)).
    pose proof (decode_range (snd r)).
    assert (forall n', 2^n <= 2^n' -> 0 <= decode (fst r) < 2^n') by (simpl in *; auto with zarith).
    assert (forall n', n <= n' -> 0 <= decode (fst r) < 2^n') by auto with zarith omega.
    autorewrite with simpl_tuple_decoder; push_decode.
    shift_left_right_t.
  Qed.
End shr.
