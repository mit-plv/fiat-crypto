(** * Reflective Pipeline *)
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Glue.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.ReflectiveTactics.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.
(** This file combines the various PHOAS modules in tactics,
    culminating in a tactic [refine_reflectively], which solves a goal of the form
<<
cast_back_flat_const (?x args) = f (cast_back_flat_const args)
 /\ Bounds.is_bounded_by ?bounds (?x args)
>>
while instantiating [?x] and [?bounds] with nicely-reduced constants.
 *)

Module Export Exports.
  Export Glue.Exports.
  Export ReflectiveTactics.Exports.
End Exports.

Ltac refine_reflectively_gen allowable_bit_widths opts :=
  refine_to_reflective_glue allowable_bit_widths;
  do_reflective_pipeline opts.

Ltac refine_reflectively128_with opts := refine_reflectively_gen [128; 256] opts.
Ltac refine_reflectively64_with opts := refine_reflectively_gen [64; 128] opts.
Ltac refine_reflectively32_with opts := refine_reflectively_gen [32; 64] opts.
Ltac refine_reflectively128_with_bool_with opts := refine_reflectively_gen [1; 128; 256] opts.
Ltac refine_reflectively64_with_bool_with opts := refine_reflectively_gen [1; 64; 128] opts.
Ltac refine_reflectively32_with_bool_with opts := refine_reflectively_gen [1; 32; 64] opts.
Ltac refine_reflectively128_with_uint8_with opts := refine_reflectively_gen [8; 128; 256] opts.
Ltac refine_reflectively64_with_uint8_with opts := refine_reflectively_gen [8; 64; 128] opts.
Ltac refine_reflectively32_with_uint8_with opts := refine_reflectively_gen [8; 32; 64] opts.
Ltac refine_reflectively128 := refine_reflectively128_with default_PipelineOptions.
Ltac refine_reflectively64 := refine_reflectively64_with default_PipelineOptions.
Ltac refine_reflectively32 := refine_reflectively32_with default_PipelineOptions.
Ltac refine_reflectively128_with_bool := refine_reflectively128_with_bool_with default_PipelineOptions.
Ltac refine_reflectively64_with_bool := refine_reflectively64_with_bool_with default_PipelineOptions.
Ltac refine_reflectively32_with_bool := refine_reflectively32_with_bool_with default_PipelineOptions.
Ltac refine_reflectively128_with_uint8 := refine_reflectively128_with_uint8_with default_PipelineOptions.
Ltac refine_reflectively64_with_uint8 := refine_reflectively64_with_uint8_with default_PipelineOptions.
Ltac refine_reflectively32_with_uint8 := refine_reflectively32_with_uint8_with default_PipelineOptions.

(** Convenience notations for options *)
Definition anf := {| Pipeline.Definition.anf := true ; Pipeline.Definition.adc_fusion := true |}.
Definition anf_without_adc_fusion := {| Pipeline.Definition.anf := true ; Pipeline.Definition.adc_fusion := false |}.
Definition adc_fusion := {| Pipeline.Definition.anf := true ; Pipeline.Definition.adc_fusion := false |}.
Definition default := default_PipelineOptions.

(** The default *)
Ltac refine_reflectively_with_bool_with opts := refine_reflectively64_with_bool_with opts.
Ltac refine_reflectively_with_uint8_with opts := refine_reflectively64_with_uint8_with opts.
Ltac refine_reflectively_with opts := refine_reflectively64_with opts.
Ltac refine_reflectively := refine_reflectively_with default.
