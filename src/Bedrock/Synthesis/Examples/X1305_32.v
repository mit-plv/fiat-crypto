Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Local Definition n := 5%nat.
Local Definition s := 2^130.
Local Definition c := [(1, 5)].
Local Definition machine_wordsize := 32.
Local Definition prefix := "poly1305_"%string.

Instance names : names_of_operations.
  make_names_of_operations prefix. Defined.

Definition ops : unsaturated_solinas_reified_ops n s c machine_wordsize.
Proof. make_reified_ops. Time Defined.

Instance poly1305_bedrock2_funcs : bedrock2_unsaturated_solinas_funcs.
funcs_from_ops ops. Defined.

Instance poly1305_bedrock2_specs : bedrock2_unsaturated_solinas_specs.
specs_from_ops ops n s c. Defined.

Instance poly1305_bedrock2_correctness :
  bedrock2_unsaturated_solinas_correctness.
prove_correctness ops n s c machine_wordsize. Defined.
(*
Eval cbv [add poly1305_bedrock2] in add.
Eval cbv [spec_of_add poly1305_bedrock2] in spec_of_add.
*)
