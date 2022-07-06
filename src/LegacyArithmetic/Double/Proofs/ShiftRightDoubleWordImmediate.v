Require Import Coq.ZArith.ZArith.
Require Import Crypto.LegacyArithmetic.Interface.
Require Import Crypto.LegacyArithmetic.Double.Core.
Require Import Crypto.LegacyArithmetic.Double.Proofs.Decode.
Require Import Crypto.LegacyArithmetic.Double.Proofs.ShiftLeftRightTactic.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Pow2Mod.
Require Import Crypto.Util.ZUtil.Definitions.

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

  Local Ltac zutil_arith ::= solve [ auto with nocore lia ].

  Global Instance is_shift_right_doubleword_immediate_double : is_shift_right_doubleword_immediate (shrd_double n).
  Proof using isdecode isshrd.
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
    assert (forall n' x, n <= n' -> 0 <= x < 2^n -> 0 <= x < 2^n') by auto with zarith lia.
    autorewrite with simpl_tuple_decoder; push_decode.
    shift_left_right_t.
  Qed.
End shrd.

Module Export Hints.
  Export Crypto.LegacyArithmetic.Interface.Hints.
  Export Crypto.LegacyArithmetic.Double.Core.Hints.
  Export Crypto.LegacyArithmetic.Double.Proofs.Decode.Hints.
  Export Crypto.LegacyArithmetic.Double.Proofs.ShiftLeftRightTactic.Hints.
  Export Crypto.Util.ZUtil.Hints.Core.
  Export Crypto.Util.ZUtil.Pow2Mod.Hints.
  Export Crypto.Util.ZUtil.Definitions.Hints.
  Global Existing Instance is_shift_right_doubleword_immediate_double.
End Hints.
