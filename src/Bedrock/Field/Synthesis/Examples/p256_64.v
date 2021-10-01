Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Local Open Scope Z_scope.

Local Existing Instances default_parameters default_parameters_ok.
Local Definition m := 2^256 - 2^224 + 2^192 + 2^96 - 1.
Local Definition prefix := "p256_"%string. (* placed before function names *)

Instance names : names_of_operations.
Proof.  make_names_of_operations prefix. Defined.

Definition ops : wbwmontgomery_reified_ops m.
Proof.  make_reified_ops. Time Defined.

Instance p256_bedrock2_funcs : bedrock2_wbwmontgomery_funcs.
Proof. funcs_from_ops ops. Defined.

Instance p256_bedrock2_specs : bedrock2_wbwmontgomery_specs.
Proof. specs_from_ops ops m. Defined.

Instance p256_bedrock2_correctness : bedrock2_wbwmontgomery_correctness.
Proof. prove_correctness ops m. Qed.

(*
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Require Import bedrock2.Syntax.
Local Open Scope bedrock_expr.
Coercion expr.var : string >-> Syntax.expr.
Eval cbv [add p256_bedrock2_funcs] in add.
Eval cbv [spec_of_add p256_bedrock2_specs] in spec_of_add.
*)
