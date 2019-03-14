(** * Push-Button Synthesis Examples *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Language.
Require Import Crypto.CStringification.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.BoundsPipeline.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  CStringification.Compilers.
Import Compilers.defaults.

Import Associational Positional.

Time Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (to_associational (weight 51 1) 5) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Time Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (scmul (weight 51 1) 5) in
              exact r)
               (None, (Some (repeat (@None _) 5), tt))
               ZRange.type.base.option.None).

Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f => carry_mulmod 51 1 (2^255) [(1,19)] 5 (seq 0 5 ++ [0; 1])%list%nat f f) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_mulx_u64"
        true None [64; 128]
        ltac:(let r := Reify (Arithmetic.mulx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
               (Some r[0~>2^64-1], Some r[0~>2^64-1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_addcarryx_u64"
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.addcarryx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_addcarryx_u51"
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.addcarryx 51) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_subborrowx_u64"
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.subborrowx 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).
Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_subborrowx_u51"
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.subborrowx 51) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_cmovznz64"
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.cmovznz 64) in
              exact r)
               (fun _ _ => [])
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange).
