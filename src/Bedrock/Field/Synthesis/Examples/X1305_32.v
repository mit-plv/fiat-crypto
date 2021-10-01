Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Local Existing Instances default_parameters default_parameters_ok.
Local Definition n := 5%nat.
Local Definition s := 2^130.
Local Definition c := [(1, 5)].
Local Definition prefix := "poly1305_"%string.

Instance names : names_of_operations.
  make_names_of_operations prefix. Defined.

Definition ops : unsaturated_solinas_reified_ops n s c.
Proof. make_reified_ops. Time Defined.

Instance poly1305_bedrock2_funcs : bedrock2_unsaturated_solinas_funcs.
Proof. funcs_from_ops ops. Defined.

Instance poly1305_bedrock2_specs : bedrock2_unsaturated_solinas_specs.
Proof. specs_from_ops ops n s c. Defined.

Instance poly1305_bedrock2_correctness :
  bedrock2_unsaturated_solinas_correctness.
Proof. prove_correctness ops n s c. Qed.
(*
Eval cbv [add poly1305_bedrock2_funcs] in add.
Eval cbv [spec_of_add poly1305_bedrock2_specs] in spec_of_add.
*)
