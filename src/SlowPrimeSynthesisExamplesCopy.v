Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Crypto.PushButtonSynthesis.SaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.Stringification.C.
Require Crypto.Stringification.Go.
Require Crypto.Stringification.Java.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Coq.ZArith.Znat.

Require Import Crypto.Util.Notations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations. Local Open Scope Z_scope.

Import
  AbstractInterpretation.Compilers
  Language.Compilers
  Language.API.Compilers.

Import Language.API.Compilers.API.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := None.
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.

Local Existing Instance default_output_options.

Module debugging_mul.
  Import Crypto.Arithmetic.Saturated.
  Import Stringification.C.
  Import Stringification.C.Compilers.
  Import Stringification.C.Compilers.ToString.

  Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.
  Local Instance : only_signed_opt := false.
  Local Instance : no_select_opt := false.
  Local Instance : static_opt := true.
  Local Instance : internal_static_opt := true.
  Local Instance : inline_opt := true.
  Local Instance : inline_internal_opt := true.
  Local Instance : use_mul_for_cmovznz_opt := false.
  Local Instance : emit_primitives_opt := true.
  Local Instance : should_split_mul_opt := false.
  Local Instance : should_split_multiret_opt := false.
  Local Instance : widen_carry_opt := false.
  Local Instance : widen_bytes_opt := true. (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)

  Let s := 2^256.
  Let c := [(1, 38)].
  Let machine_wordsize := 64.
  
  Let possible_values := prefix_with_carry [machine_wordsize].
  Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
  Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
  Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

  Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Let m : nat := Z.to_nat (2*n).

  Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
  Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound n.

  Let out_bound := Some r[0 ~> (2^(machine_wordsize*2) - 1)]%zrange.
  Let out_boundsn : list (ZRange.type.option.interp base.type.Z)
                         := repeat out_bound n.

  Compute possible_values.
  Compute (weight machine_wordsize 1).
    
  Time Compute
       Show.show
       (Pipeline.BoundsPipelineToString
          "fiat" "mul"
          false
          false
          None
          possible_values
          machine_wordsize
          ltac:(let n := (eval cbv in n) in
                let m := (eval cbv in m) in
                let r := Reify (@Saturated.Rows.mul (weight machine_wordsize 1) (2^machine_wordsize) n m) in
                exact r)
                 (fun _ _ => [])
                 (Some boundsn, (Some boundsn, tt))
                 (Some boundsn, None)
                 (None, (None, tt))
                 (None, None)
         : Pipeline.ErrorT _).

End debugging_mul.
