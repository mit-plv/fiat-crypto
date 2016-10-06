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

Section shrd.
  Context (n : Z) {W}
          {ldi : load_immediate W}
          {shrd : shift_right_doubleword_immediate W}
          {decode : decoder n W}
          {isdecode : is_decode decode}
          {isldi : is_load_immediate ldi}
          {isshrd : is_shift_right_doubleword_immediate shrd}.

  Local Ltac zutil_arith ::= solve [ auto with nocore omega ].

  Global Instance is_shift_right_doubleword_immediate_double : is_shift_right_doubleword_immediate (shrd_double n).
  Proof.
    intros high low count Hcount; hnf in Hcount.
    unfold shrd_double, shift_right_doubleword_immediate_double; simpl.
    generalize (decode_range low).
    generalize (decode_range high).
    generalize (decode_range (fst low)).
    generalize (decode_range (snd low)).
    generalize (decode_range (fst high)).
    generalize (decode_range (snd high)).
    assert (forall x, 0 <= Z.pow2_mod x n < 2^n) by auto with zarith.
    assert (forall n' x, 2^n <= 2^n' -> 0 <= x < 2^n -> 0 <= x < 2^n') by auto with zarith.
    assert (forall n' x, n <= n' -> 0 <= x < 2^n -> 0 <= x < 2^n') by auto with zarith omega.
    autorewrite with simpl_tuple_decoder; push_decode.
    shift_left_right_t.
  Qed.
End shrd.
