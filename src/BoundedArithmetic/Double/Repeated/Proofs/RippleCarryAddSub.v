Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.RippleCarryAddSub.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Decode.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Arguments Z.mul !_ !_.
Local Arguments Z.pow : simpl never.
Local Arguments Z.of_nat : simpl never.
Local Opaque tuple_decoder.

Section add_with_carry.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {adc : add_with_carry W}
          {is_adc : is_add_with_carry adc}.

  Fixpoint is_add_with_carry_repeated_double {exp : nat} : is_add_with_carry (add_with_carry_repeated_double (exp:=exp)).
  Proof. is_cls_fixpoint_t decode n exp is_adc (@is_add_with_carry_repeated_double). Qed.
  Global Existing Instance is_add_with_carry_repeated_double.
End add_with_carry.

Section sub_with_carry.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {subc : sub_with_carry W}
          {is_subc : is_sub_with_carry subc}.

  Fixpoint is_sub_with_carry_repeated_double {exp : nat} : is_sub_with_carry (sub_with_carry_repeated_double (exp:=exp)).
  Proof. is_cls_fixpoint_t decode n exp is_subc (@is_sub_with_carry_repeated_double). Qed.
  Global Existing Instance is_sub_with_carry_repeated_double.
End sub_with_carry.
