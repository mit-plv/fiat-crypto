Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.BitwiseOr.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Decode.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Arguments Z.mul !_ !_.
Local Arguments Z.pow : simpl never.
Local Arguments Z.of_nat : simpl never.
Local Opaque tuple_decoder.

Section bitwise_or.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {or : bitwise_or W}
          {is_or : is_bitwise_or or}.

  Fixpoint is_bitwise_or_repeated_double {exp : nat} : is_bitwise_or (bitwise_or_repeated_double (exp:=exp)).
  Proof. is_cls_fixpoint_t decode n exp is_or (@is_bitwise_or_repeated_double). Qed.
  Global Existing Instance is_bitwise_or_repeated_double.
End bitwise_or.
