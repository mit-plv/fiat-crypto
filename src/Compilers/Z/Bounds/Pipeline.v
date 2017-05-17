(** * Reflective Pipeline *)
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Glue.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.ReflectiveTactics.
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

Ltac refine_reflectively128_with opts := refine_reflectively_gen (1::128::256::nil)%nat%list opts.
Ltac refine_reflectively64_with opts := refine_reflectively_gen (1::64::128::nil)%nat%list opts.
Ltac refine_reflectively32_with opts := refine_reflectively_gen (1::32::64::nil)%nat%list opts.
Ltac refine_reflectively128 := refine_reflectively128_with default_PipelineOptions.
Ltac refine_reflectively64 := refine_reflectively64_with default_PipelineOptions.
Ltac refine_reflectively32 := refine_reflectively32_with default_PipelineOptions.

(** Convenience notations for options *)
Definition anf := {| Pipeline.Definition.anf := true |}.

(** The default *)
Ltac refine_reflectively_with opts := refine_reflectively64_with opts.
Ltac refine_reflectively := refine_reflectively_with default_PipelineOptions.
