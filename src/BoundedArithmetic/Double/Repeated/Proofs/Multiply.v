Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Multiply.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.LoadImmediate.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.RippleCarryAddSub.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.ShiftLeftRight.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Arguments Z.mul !_ !_.
Local Arguments Z.pow : simpl never.
Local Arguments Z.of_nat : simpl never.
Local Opaque tuple_decoder.

Section multiply_double.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {ldi : load_immediate W}
          {isldi : is_load_immediate ldi}
          {shl : shift_left_immediate W}
          {isshl : is_shift_left_immediate shl}
          {shr : shift_right_immediate W}
          {isshr : is_shift_right_immediate shr}
          {or : bitwise_or W}
          {isor : is_bitwise_or or}
          {adc : add_with_carry W}
          {isadc : is_add_with_carry adc}
          {muldw : multiply_double W}
          {ismuldw : is_mul_double muldw}.

  Fixpoint is_multiply_double_repeated_double {exp : nat} : is_mul_double (multiply_double_repeated_double (exp:=exp)).
  Proof. is_cls_fixpoint_t decode n exp ismuldw (@is_multiply_double_repeated_double). Qed.
  Global Existing Instance is_multiply_double_repeated_double.
End multiply_double.

Section multiply.
  Context {n_over_two W}
          {decode : decoder (2 * n_over_two) W}
          {is_decode : is_decode decode}
          {ldi : load_immediate W}
          {isldi : is_load_immediate ldi}
          {shl : shift_left_immediate W}
          {isshl : is_shift_left_immediate shl}
          {shr : shift_right_immediate W}
          {isshr : is_shift_right_immediate shr}
          {or : bitwise_or W}
          {isor : is_bitwise_or or}
          {adc : add_with_carry W}
          {isadc : is_add_with_carry adc}
          {mulhwll : multiply_low_low W}
          {mulhwhl : multiply_high_low W}
          {mulhwhh : multiply_high_high W}
          {ismulhwll : is_mul_low_low n_over_two mulhwll}
          {ismulhwhl : is_mul_high_low n_over_two mulhwhl}
          {ismulhwhh : is_mul_high_high n_over_two mulhwhh}.

  Fixpoint is_multi_multiply_repeated_double {exp : nat}
    : (is_mul_low_low (Z.of_nat 2^Z.of_nat exp * n_over_two) (multiply_low_low_repeated_double (exp:=exp))
       * is_mul_high_low (Z.of_nat 2^Z.of_nat exp * n_over_two) (multiply_high_low_repeated_double (exp:=exp))
       * is_mul_high_high (Z.of_nat 2^Z.of_nat exp * n_over_two) (multiply_high_high_repeated_double (exp:=exp)))%type.
  Proof using Type*.
    destruct exp as [|exp']; [ clear is_multi_multiply_repeated_double | specialize (is_multi_multiply_repeated_double exp') ].
    { destruct decode; generalize ismulhwll, ismulhwhl, ismulhwhh.
      simpl.
      change (Z.of_nat 2 ^ Z.of_nat 0) with 1.
      generalize (eq_sym (Z.mul_1_l (2 * n_over_two))); generalize (1 * (2 * n_over_two)).
      intro; clear; induction 1.
      generalize (eq_sym (Z.mul_1_l (n_over_two))); generalize (1 * (n_over_two)).
      intro; clear; induction 1.
      intros; repeat apply pair; assumption. }
    { destruct is_multi_multiply_repeated_double as [ [ ? ? ] ? ].
      simpl @repeated_tuple_decoder; simpl;
        change (Z.of_nat (S exp')) with (Z.of_nat (1 + exp')).
      rewrite (Nat2Z.inj_add 1 exp'), Z.pow_add_r, Z.pow_1_r, (*!Z.mul_assoc, <- !(Z.mul_comm 2),*) <- !Z.mul_assoc by omega.
      rewrite <- decoder_eta by omega.
      rewrite (Z.mul_assoc (Z.of_nat 2) (_^_) n_over_two), (Z.mul_comm (Z.of_nat 2) (_^_)), <- (Z.mul_assoc (_^_) (Z.of_nat 2) n_over_two) by omega.
      repeat apply pair;
        try exact _. }
  Qed.

  Global Instance is_multiply_low_low_repeated_double {exp : nat}
    : is_mul_low_low (Z.of_nat 2^Z.of_nat exp * n_over_two) (multiply_low_low_repeated_double (exp:=exp))
    := fst (fst (@is_multi_multiply_repeated_double exp)).
  Global Instance is_multiply_high_low_repeated_double {exp : nat}
    : is_mul_high_low (Z.of_nat 2^Z.of_nat exp * n_over_two) (multiply_high_low_repeated_double (exp:=exp))
    := snd (fst (@is_multi_multiply_repeated_double exp)).
  Global Instance is_multiply_high_high_repeated_double {exp : nat}
    : is_mul_high_high (Z.of_nat 2^Z.of_nat exp * n_over_two) (multiply_high_high_repeated_double (exp:=exp))
    := snd (@is_multi_multiply_repeated_double exp).
End multiply.
