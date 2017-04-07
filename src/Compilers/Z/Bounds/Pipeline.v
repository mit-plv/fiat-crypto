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

Ltac refine_reflectively :=
  refine_to_reflective_glue;
  do_reflective_pipeline.
