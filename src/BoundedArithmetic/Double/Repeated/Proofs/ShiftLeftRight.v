Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.ShiftLeft.
Require Import Crypto.BoundedArithmetic.Double.Proofs.ShiftRight.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.LoadImmediate.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.BitwiseOr.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Arguments Z.mul !_ !_.
Local Arguments Z.pow : simpl never.
Local Arguments Z.of_nat : simpl never.
Local Opaque tuple_decoder.

Section shift_left_right.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {ldi : load_immediate W}
          {is_ldi : is_load_immediate ldi}
          {shl : shift_left_immediate W}
          {is_shl : is_shift_left_immediate shl}
          {shr : shift_right_immediate W}
          {is_shr : is_shift_right_immediate shr}
          {or : bitwise_or W}
          {is_or : is_bitwise_or or}.

  Fixpoint is_shift_left_right_immediate_repeated_double {exp : nat}
    : (is_shift_left_immediate (shift_left_immediate_repeated_double (exp:=exp))
       * is_shift_right_immediate (shift_right_immediate_repeated_double (exp:=exp)))%type.
  Proof using Type*. is_cls_fixpoint_t2 decode n exp is_shl is_shr (@is_shift_left_right_immediate_repeated_double). Qed.
  Global Instance is_shift_left_immediate_repeated_double {exp : nat}
    : is_shift_left_immediate (shift_left_immediate_repeated_double (exp:=exp))
    := fst (@is_shift_left_right_immediate_repeated_double exp).
  Global Instance is_shift_right_immediate_repeated_double {exp : nat}
    : is_shift_right_immediate (shift_right_immediate_repeated_double (exp:=exp))
    := snd (@is_shift_left_right_immediate_repeated_double exp).
End shift_left_right.
