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

Ltac refine_reflectively_gen allowable_bit_widths :=
  refine_to_reflective_glue allowable_bit_widths;
  do_reflective_pipeline.

Ltac refine_reflectively128 := refine_reflectively_gen (128::256::nil)%nat%list.
Ltac refine_reflectively64 := refine_reflectively_gen (64::128::nil)%nat%list.
Ltac refine_reflectively32 := refine_reflectively_gen (32::64::nil)%nat%list.

(** The default *)
Ltac refine_reflectively := refine_reflectively64.
