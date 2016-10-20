(** * Strip CF for Interface for bounded arithmetic *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.

Local Open Scope type_scope.
Local Open Scope Z_scope.

Section strip_CF.
  Context (n : Z) (* bit-width of width of [W] *)
          {W : Type} (* bounded type, [W] for word *)
          (Wdecoder : decoder n W).
  Local Notation imm := Z (only parsing). (* immediate (compile-time) argument *)

  Global Instance shift_right_doubleword_immediate_strip_CF
         {shrdf : shift_right_doubleword_immediate_with_CF W}
    : shift_right_doubleword_immediate W
    := { shrd x y z := snd (shrdf x y z) }.
  Global Instance is_shift_right_doubleword_immediate_strip_CF
         {shrdf : shift_right_doubleword_immediate_with_CF W}
         {shift_right_doubleword_immediate_with_CF : is_shift_right_doubleword_immediate_with_CF shrdf}
    : is_shift_right_doubleword_immediate shift_right_doubleword_immediate_strip_CF
    := shift_right_doubleword_immediate_with_CF.

  Global Instance shift_left_immediate_strip_CF
         {shlf : shift_left_immediate_with_CF W}
    : shift_left_immediate W
    := { shl x y := snd (shlf x y) }.
  Global Instance is_shift_left_immediate_strip_CF
         {shlf : shift_left_immediate_with_CF W}
         {shift_left_immediate_with_CF : is_shift_left_immediate_with_CF shlf}
    : is_shift_left_immediate shift_left_immediate_strip_CF
    := shift_left_immediate_with_CF.

  Global Instance shift_right_immediate_strip_CF
         {shrf : shift_right_immediate_with_CF W}
    : shift_right_immediate W
    := { shr x y := snd (shrf x y) }.
  Global Instance is_shift_right_immediate_strip_CF
         {shrf : shift_right_immediate_with_CF W}
         {shift_right_immediate_with_CF : is_shift_right_immediate_with_CF shrf}
    : is_shift_right_immediate shift_right_immediate_strip_CF
    := shift_right_immediate_with_CF.

  Global Instance bitwise_and_strip_CF
         {andf : bitwise_and_with_CF W}
    : bitwise_and W
    := { and x y := snd (andf x y) }.
  Global Instance is_bitwise_and_strip_CF
         {andf : bitwise_and_with_CF W}
         {bitwise_and_with_CF : is_bitwise_and_with_CF andf}
    : is_bitwise_and bitwise_and_strip_CF
    := { decode_bitwise_and := @decode_snd_bitwise_and_with_CF _ _ _ _ bitwise_and_with_CF }.

  Global Instance bitwise_or_strip_CF
         {orf : bitwise_or_with_CF W}
    : bitwise_or W
    := { or x y := snd (orf x y) }.
  Global Instance is_bitwise_or_strip_CF
         {orf : bitwise_or_with_CF W}
         {bitwise_or_with_CF : is_bitwise_or_with_CF orf}
    : is_bitwise_or bitwise_or_strip_CF
    := { decode_bitwise_or := @decode_snd_bitwise_or_with_CF _ _ _ _ bitwise_or_with_CF }.

  Global Instance multiply_double_strip_CF
         {muldwf : multiply_double_with_CF W}
    : multiply_double W
    := { muldw x y := snd (muldwf x y) }.
  Global Instance is_mul_double_strip_CF
         {muldwf : multiply_double_with_CF W}
         {multiply_double_with_CF : is_mul_double_with_CF muldwf}
    : is_mul_double multiply_double_strip_CF
    := { decode_fst_mul_double := @decode_fst_mul_double_with_CF _ _ _ _ multiply_double_with_CF;
         decode_snd_mul_double := @decode_snd_mul_double_with_CF _ _ _ _ multiply_double_with_CF}.
End strip_CF.
