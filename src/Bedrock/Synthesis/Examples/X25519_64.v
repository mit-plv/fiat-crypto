Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Let n := 10%nat.
Let s := 2^255.
Let c := [(1, 19)].
Let machine_wordsize := 64.
Let prefix := "curve25519_"%string. (* placed before function names *)

Definition names : names_of_operations.
make_names_of_operations prefix. Defined.

Local Instance curve25519_bedrock2_scmul121665
  : bedrock2_unsaturated_solinas_scmul 121665.
Proof.
  let p := parameters_from_wordsize machine_wordsize in
  make_bedrock2_unsaturated_solinas_scmul p names n s c machine_wordsize.
Defined.

Local Instance curve25519_bedrock2_scmul121666
  : bedrock2_unsaturated_solinas_scmul 121666.
Proof.
  let p := parameters_from_wordsize machine_wordsize in
  make_bedrock2_unsaturated_solinas_scmul p names n s c machine_wordsize.
Defined.

Instance curve25519_bedrock2 : bedrock2_unsaturated_solinas.
Proof.
  let p := parameters_from_wordsize machine_wordsize in
  make_bedrock2_unsaturated_solinas p names n s c machine_wordsize.
Time Defined.
(*
Eval cbv [add curve25519_bedrock2] in add.
Eval cbv [spec_of_add curve25519_bedrock2] in spec_of_add.
*)
