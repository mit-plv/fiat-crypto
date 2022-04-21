(** * Push-Button Synthesis Examples *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional.

Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := [].
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f g => mulmod (weight 51 1) (2^255) [(1,19)] 5 f g) in
              exact r)
               (Some (repeat (@None _) 5), ((Some (repeat (@None _) 5), tt)))
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f g => mulmod (weight 51 2) (2^255) [(1,19)] 10 f g) in
              exact r)
               (Some (repeat (@None _) 10), ((Some (repeat (@None _) 10), tt)))
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (to_associational (weight 51 1) 5) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (scmul (weight 51 1) 5) in
              exact r)
               (None, (Some (repeat (@None _) 5), tt))
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f => carry_mulmod 51 1 (2^255) [(1,19)] 5 (seq 0 5 ++ [0; 1])%list%nat f f) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Local Existing Instance ToString.C.OutputCAPI.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Existing Instance default_output_options.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : inline_opt := true.
Local Instance : inline_internal_opt := true.
Local Instance : emit_primitives_opt := true.

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_mulx_u64"
        true true None [64; 128] 64
        ltac:(let r := Reify (mulx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
               (Some r[0~>2^64-1], Some r[0~>2^64-1])%zrange
               (None, (None, tt))
               (None, None)
   : Pipeline.ErrorT _).

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_addcarryx_u64"
        true true None [1; 64; 128] 64
        ltac:(let r := Reify (addcarryx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange
               (None, (None, (None, tt)))
               (None, None)
   : Pipeline.ErrorT _).

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_addcarryx_u51"
        true true None [1; 64; 128] 64
        ltac:(let r := Reify (addcarryx 51) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange
               (None, (None, (None, tt)))
               (None, None)
   : Pipeline.ErrorT _).

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_subborrowx_u64"
        true true None [1; 64; 128] 64
        ltac:(let r := Reify (subborrowx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange
               (None, (None, (None, tt)))
               (None, None)
   : Pipeline.ErrorT _).
Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_subborrowx_u51"
        true true None [1; 64; 128] 64
        ltac:(let r := Reify (subborrowx 51) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange
               (None, (None, (None, tt)))
               (None, None)
   : Pipeline.ErrorT _).

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_cmovznz64"
        true true None [1; 64; 128] 64
        ltac:(let r := Reify (cmovznz 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange
               (None, (None, (None, tt)))
               None
   : Pipeline.ErrorT _).
