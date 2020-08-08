Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Local Open Scope Z_scope.

Local Definition m := 2^224 - 2^96 + 1.
Local Definition machine_wordsize := 64.
Local Definition prefix := "p224_"%string. (* placed before function names *)

Instance names : names_of_operations.
  make_names_of_operations prefix. Defined.

Definition ops : wbwmontgomery_reified_ops m machine_wordsize.
  make_reified_ops. Time Defined.

Instance p224_bedrock2_funcs : bedrock2_wbwmontgomery_funcs.
funcs_from_ops ops. Defined.

Instance p224_bedrock2_specs : bedrock2_wbwmontgomery_specs.
specs_from_ops ops m. Defined.

Instance p224_bedrock2_correctness : bedrock2_wbwmontgomery_correctness.
prove_correctness ops m machine_wordsize. Defined.

(*
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Require Import bedrock2.Syntax.
Coercion expr.var : string >-> Syntax.expr.
Local Open Scope bedrock_expr.
Eval cbv [add p224_bedrock2_funcs] in add.
Eval cbv [spec_of_add p224_bedrock2_specs] in spec_of_add.
*)
