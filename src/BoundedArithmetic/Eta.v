(** * Bounded arithmetic η expansion *)
(** This is useful for allowing us to refold the projections. *)
Require Import Crypto.BoundedArithmetic.Interface.

Definition eta_decode {n W} (x : decoder n W) : decoder n W := {| decode := decode |}.
Section InstructionGallery.
  Context {n W} {Wdecoder : decoder n W}.
  Definition eta_ldi (x : load_immediate W) := {| ldi := ldi |}.
  Definition eta_shrd (x : shift_right_doubleword_immediate W) := {| shrd := shrd |}.
  Definition eta_shrdf (x : shift_right_doubleword_immediate_with_CF W) := {| shrdf := shrdf |}.
  Definition eta_shl (x : shift_left_immediate W) := {| shl := shl |}.
  Definition eta_shlf (x : shift_left_immediate_with_CF W) := {| shlf := shlf |}.
  Definition eta_shr (x : shift_right_immediate W) := {| shr := shr |}.
  Definition eta_shrf (x : shift_right_immediate_with_CF W) := {| shrf := shrf |}.
  Definition eta_sprl (x : spread_left_immediate W) := {| sprl := sprl |}.
  Definition eta_mkl (x : mask_keep_low W) := {| mkl := mkl |}.
  Definition eta_and (x : bitwise_and W) := {| and := and |}.
  Definition eta_andf (x : bitwise_and_with_CF W) := {| andf := andf |}.
  Definition eta_or (x : bitwise_or W) := {| or := or |}.
  Definition eta_orf (x : bitwise_or_with_CF W) := {| orf := orf |}.
  Definition eta_adc (x : add_with_carry W) := {| adc := adc |}.
  Definition eta_subc (x : sub_with_carry W) := {| subc := subc |}.
  Definition eta_mul (x : multiply W) := {| mul := mul |}.
  Definition eta_mulhwll (x : multiply_low_low W) := {| mulhwll := mulhwll |}.
  Definition eta_mulhwhl (x : multiply_high_low W) := {| mulhwhl := mulhwhl |}.
  Definition eta_mulhwhh (x : multiply_high_high W) := {| mulhwhh := mulhwhh |}.
  Definition eta_muldw (x : multiply_double W) := {| muldw := muldw |}.
  Definition eta_muldwf (x : multiply_double_with_CF W) := {| muldwf := muldwf |}.
  Definition eta_selc (x : select_conditional W) := {| selc := selc |}.
  Definition eta_addm (x : add_modulo W) := {| addm := addm |}.
End InstructionGallery.

Declare Reduction unfold_eta_bounded_instructions
  := cbv [eta_decode eta_ldi eta_shrd eta_shrdf eta_shl eta_shlf eta_shr eta_shrf eta_sprl eta_mkl eta_and eta_andf eta_or eta_orf eta_adc eta_subc eta_mul eta_mulhwll eta_mulhwhl eta_mulhwhh eta_muldw eta_muldwf eta_selc eta_addm].

Module fancy_machine.
  Import Interface.fancy_machine.
  Definition eta_instructions {n} (x : fancy_machine.instructions n) : fancy_machine.instructions n
    := Eval unfold_eta_bounded_instructions in
        {| W := W;
           decode := eta_decode decode;
           ldi := eta_ldi ldi;
           shrd := eta_shrd shrd;
           shl := eta_shl shl;
           shr := eta_shr shr;
           adc := eta_adc adc;
           subc := eta_subc subc;
           mulhwll := eta_mulhwll mulhwll;
           mulhwhl := eta_mulhwhl mulhwhl;
           mulhwhh := eta_mulhwhh mulhwhh;
           selc := eta_selc selc;
           addm := eta_addm addm |}.
End fancy_machine.

Module x86.
  Import Interface.x86.
  Definition eta_instructions {n} (x : x86.instructions n) : x86.instructions n
    := Eval unfold_eta_bounded_instructions in
        {| W := W;
           decode := eta_decode decode;
           ldi := eta_ldi ldi;
           shrdf := eta_shrdf shrdf;
           shlf := eta_shlf shlf;
           shrf := eta_shrf shrf;
           adc := eta_adc adc;
           subc := eta_subc subc;
           muldwf := eta_muldwf muldwf;
           selc := eta_selc selc;
           orf := eta_orf orf |}.
End x86.
