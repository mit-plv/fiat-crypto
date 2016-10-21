(*** Implementing Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.

Fixpoint repeated_tuple W (base : nat) (exp : nat)
  := match exp with
     | O => W
     | S exp' => tuple (repeated_tuple W base exp') base
     end.

Local Arguments Z.mul !_ !_.
Local Opaque tuple_decoder.

Section decode.
  Context {n W}
          {decode : decoder n W}
          {base : nat}.

  Fixpoint repeated_tuple_decoder {exp : nat}
    : decoder (base^exp * n) (repeated_tuple W base exp)
    := {| Interface.decode
          := match exp return repeated_tuple W base exp -> Z with
             | O => decode
             | S exp' => Interface.decode : tuple (repeated_tuple W base exp') base -> Z
             end |}.
  Global Existing Instance repeated_tuple_decoder.
End decode.

Section all.
  Context {n W}
          {decode : decoder n W}
          {ldi : load_immediate W}
          {shrd : shift_right_doubleword_immediate W}
          {sprl : spread_left_immediate W}
          {shl : shift_left_immediate W}
          {shr : shift_right_immediate W}
          {mkl : mask_keep_low W}
          {and : bitwise_and W}
          {or : bitwise_or W}
          {adc : add_with_carry W}
          {subc : sub_with_carry W}
          {mul : multiply W}
          {mulhwll : multiply_low_low W}
          {mulhwhl : multiply_high_low W}
          {mulhwhh : multiply_high_high W}
          {muldw : multiply_double W}
          {selc : select_conditional W}
          {addm : add_modulo W}.

  Local Notation repeated_tuple_cls cls exp
    := (match exp%nat as exp0 return cls (repeated_tuple W 2 exp0) with
        | O => _ : cls W
        | S exp' => _ : cls (tuple (repeated_tuple W 2 exp') 2)
        end) (only parsing).

  Fixpoint load_immediate_repeated_double {exp : nat}
    := repeated_tuple_cls load_immediate exp.
  Global Existing Instance load_immediate_repeated_double.
  Fixpoint shift_right_doubleword_immediate_repeated_double {exp : nat}
    := repeated_tuple_cls shift_right_doubleword_immediate exp.
  Global Existing Instance shift_right_doubleword_immediate_repeated_double.
  (*Fixpoint spread_left_immediate_repeated_double {exp : nat}
    := repeated_tuple_cls spread_left_immediate exp.
  Global Existing Instance spread_left_immediate_repeated_double.*)
  Fixpoint bitwise_or_repeated_double {exp : nat}
    := repeated_tuple_cls bitwise_or exp.
  Global Existing Instance bitwise_or_repeated_double.
  Local Hint Extern 1 =>
  match goal with
  | [ H : forall n, (_ * _)%type |- _ ]
    => pose proof (fun n => fst (H n));
         pose proof (fun n => snd (H n));
         clear H
  end : typeclass_instances.
  Fixpoint shlr_repeated_double {exp : nat} : (shift_left_immediate (repeated_tuple W 2 exp) * shift_right_immediate (repeated_tuple W 2 exp))%type.
  Proof.
    refine (repeated_tuple_cls (fun T => shift_left_immediate T * shift_right_immediate T)%type exp);
      split; exact _.
  Defined.
  Global Instance shift_left_immediate_repeated_double {exp : nat} : shift_left_immediate (repeated_tuple W 2 exp)
    := fst (@shlr_repeated_double exp).
  Global Instance shift_right_immediate_repeated_double {exp : nat} : shift_right_immediate (repeated_tuple W 2 exp)
    := snd (@shlr_repeated_double exp).
  (*Fixpoint mask_keep_low_repeated_double {exp : nat}
    := repeated_tuple_cls mask_keep_low exp.
  Global Existing Instance mask_keep_low_repeated_double.*)
  Fixpoint bitwise_and_repeated_double {exp : nat}
    := repeated_tuple_cls bitwise_and exp.
  Global Existing Instance bitwise_and_repeated_double.
  Fixpoint add_with_carry_repeated_double {exp : nat}
    := repeated_tuple_cls add_with_carry exp.
  Global Existing Instance add_with_carry_repeated_double.
  Fixpoint sub_with_carry_repeated_double {exp : nat}
    := repeated_tuple_cls sub_with_carry exp.
  Global Existing Instance sub_with_carry_repeated_double.
  (*Fixpoint multiply_repeated_double {exp : nat}
    := repeated_tuple_cls multiply exp.
  Global Existing Instance multiply_repeated_double.*)
  Fixpoint multiply_double_repeated_double {exp : nat}
    := repeated_tuple_cls multiply_double exp.
  Global Existing Instance multiply_double_repeated_double.
  Fixpoint multiply_low_low_repeated_double {exp : nat}
    := repeated_tuple_cls multiply_low_low exp.
  Global Existing Instance multiply_low_low_repeated_double.
  Fixpoint multiply_high_low_repeated_double {exp : nat}
    := repeated_tuple_cls multiply_high_low exp.
  Global Existing Instance multiply_high_low_repeated_double.
  Fixpoint multiply_high_high_repeated_double {exp : nat}
    := repeated_tuple_cls multiply_high_high exp.
  Global Existing Instance multiply_high_high_repeated_double.
  Fixpoint select_conditional_repeated_double {exp : nat}
    := repeated_tuple_cls select_conditional exp.
  Global Existing Instance select_conditional_repeated_double.
  (*Fixpoint add_modulo_repeated_double {exp : nat}
    := repeated_tuple_cls add_modulo exp.
  Global Existing Instance add_modulo_repeated_double.*)
End all.
