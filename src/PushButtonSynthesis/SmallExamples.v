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

Local Existing Instance ToString.C.OutputCAPI.
Local Instance machine_wordsize : machine_wordsize_opt := 64.
Local Existing Instance Pipeline.default_BaseOptions.
Local Existing Instance Pipeline.default_DerivedOptions.
Local Existing Instance Pipeline.default_ExtendedOptions.
(* sanity check for lack of evars *)
Goal True. pose Pipeline.BoundsPipeline as check_evar_free. Abort.

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify (fun f g => mulmod (weight 51 1) (2^255) [(1,19)] 5 f g) in
              exact r)
               (Some (repeat (@None _) 5), ((Some (repeat (@None _) 5), tt)))
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify (fun f g => mulmod (weight 51 2) (2^255) [(1,19)] 10 f g) in
              exact r)
               (Some (repeat (@None _) 10), ((Some (repeat (@None _) 10), tt)))
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify (to_associational (weight 51 1) 5) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify (scmul (weight 51 1) 5) in
              exact r)
               (None, (Some (repeat (@None _) 5), tt))
               ZRange.type.base.option.None).

Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify (fun f => carry_mulmod 51 1 (2^255) [(1,19)] 5 (seq 0 5 ++ [0; 1])%list%nat f f) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

(* sanity check for lack of evars *)
Goal True. pose Pipeline.BoundsPipelineToString as check_evar_free. Abort.

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "fiat_mulx_u64"
        true [64; 128]
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
        true [1; 64; 128]
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
        true [1; 64; 128]
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
        true [1; 64; 128]
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
        true [1; 64; 128]
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
        true [1; 64; 128]
        ltac:(let r := Reify (cmovznz 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange
               (None, (None, (None, tt)))
               None
   : Pipeline.ErrorT _).
