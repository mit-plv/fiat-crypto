Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Translation.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Local Definition n := 10%nat.
Local Definition s := 2^255.
Local Definition c := [(1, 19)].
Local Definition machine_wordsize := 32.
Local Definition prefix := "curve25519_"%string. (* placed before function names *)

Instance names : names_of_operations.
  make_names_of_operations prefix. Defined.

Definition ops : unsaturated_solinas_reified_ops n s c machine_wordsize.
Proof. make_reified_ops. Time Defined.

Instance curve25519_bedrock2_funcs : bedrock2_unsaturated_solinas_funcs.
funcs_from_ops ops. Defined.

Instance curve25519_bedrock2_specs : bedrock2_unsaturated_solinas_specs.
specs_from_ops ops n s c. Defined.

Instance curve25519_bedrock2_correctness :
  bedrock2_unsaturated_solinas_correctness.
prove_correctness ops n s c machine_wordsize. Defined.

(*
Require Import bedrock2.ToCString.
Compute c_func UnsaturatedSolinas.to_bytes.
Compute c_func UnsaturatedSolinas.carry_mul.
*)
