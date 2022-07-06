Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.LegacyArithmetic.Interface.
Require Import Crypto.LegacyArithmetic.Double.Core.
Require Import Crypto.LegacyArithmetic.Double.Proofs.Decode.
Require Import Crypto.LegacyArithmetic.Double.Proofs.ShiftLeftRightTactic.
Require Import Crypto.Util.ZUtil.Pow2Mod.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.

Local Open Scope Z_scope.

Local Opaque tuple_decoder.
Local Arguments Z.pow !_ !_.
Local Arguments Z.mul !_ !_.

Section shl.
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

  Global Instance is_shift_left_immediate_double : is_shift_left_immediate (shl_double n).
  Proof using Type*.
    intros r count H; hnf in H.
    assert (0 < 2^count) by auto with zarith.
    assert (0 < 2^(n+count)) by auto with zarith.
    assert (forall x, 0 <= Z.pow2_mod x n < 2^n) by auto with zarith.
    unfold shl_double; simpl.
    generalize (decode_range r).
    pose proof (decode_range (fst r)).
    pose proof (decode_range (snd r)).
    assert (forall n', 2^n <= 2^n' -> 0 <= decode (fst r) < 2^n') by (simpl in *; auto with zarith).
    assert (forall n', n <= n' -> 0 <= decode (fst r) < 2^n') by auto with zarith lia.
    autorewrite with simpl_tuple_decoder; push_decode.
    shift_left_right_t.
  Qed.
End shl.

Module Export Hints.
  Export Crypto.LegacyArithmetic.Interface.Hints.
  Export Crypto.LegacyArithmetic.Double.Core.Hints.
  Export Crypto.LegacyArithmetic.Double.Proofs.Decode.Hints.
  Export Crypto.LegacyArithmetic.Double.Proofs.ShiftLeftRightTactic.Hints.
  Export Crypto.Util.ZUtil.Pow2Mod.Hints.
  Export Crypto.Util.ZUtil.Pow.Hints.
  Export Crypto.Util.ZUtil.Hints.ZArith.
  Export Crypto.Util.ZUtil.Notations.Hints.
  Export Crypto.Util.ZUtil.Definitions.Hints.
  Global Existing Instance is_shift_left_immediate_double.
End Hints.
