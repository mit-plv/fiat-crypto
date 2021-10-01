Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Local Existing Instances default_parameters default_parameters_ok.
Local Definition n := 10%nat.
Local Definition s := 2^255.
Local Definition c := [(1, 19)].
Local Definition prefix := "curve25519_"%string. (* placed before function names *)

Instance names : names_of_operations.
  make_names_of_operations prefix. Defined.

Definition ops : unsaturated_solinas_reified_ops n s c.
Proof. make_reified_ops. Time Defined.

Instance curve25519_bedrock2_funcs : bedrock2_unsaturated_solinas_funcs.
Proof. funcs_from_ops ops. Defined.

Instance curve25519_bedrock2_specs : bedrock2_unsaturated_solinas_specs.
Proof. specs_from_ops ops n s c. Defined.

Instance curve25519_bedrock2_correctness :
  bedrock2_unsaturated_solinas_correctness.
Proof. prove_correctness ops n s c. Qed.

(*
Require Import bedrock2.NotationsInConstr.
Require Import bedrock2.Syntax. Import Syntax.Coercions.
Local Open Scope bedrock_expr.
Eval cbv [add curve25519_bedrock2_funcs] in add.
Eval cbv [spec_of_add curve25519_bedrock2_specs] in spec_of_add.
*)

Section Scmul121666.
  Definition reified_scmul121666 :
    unsaturated_solinas_reified_scmul n s c 121666.
  Proof. make_reified_scmul. Defined.

  Local Instance curve25519_bedrock2_scmul121666_func
    : bedrock2_unsaturated_solinas_scmul_func.
  Proof. scmul_func_from_ops reified_scmul121666. Defined.

  Local Instance curve25519_bedrock2_scmul121666_spec
    : bedrock2_unsaturated_solinas_scmul_spec.
  Proof. scmul_spec_from_ops reified_scmul121666 n s c. Defined.

  Local Instance curve25519_bedrock2_scmul121666_correctness :
    bedrock2_unsaturated_solinas_scmul_correctness.
  Proof. prove_correctness_scmul reified_scmul121666 n s c. Qed.
End Scmul121666.

Section Scmul121665.
  Definition reified_scmul121665 :
    unsaturated_solinas_reified_scmul n s c 121665.
  Proof. make_reified_scmul. Defined.

  Local Instance curve25519_bedrock2_scmul121665_func
    : bedrock2_unsaturated_solinas_scmul_func.
  Proof. scmul_func_from_ops reified_scmul121665. Defined.

  Local Instance curve25519_bedrock2_scmul121665_spec
    : bedrock2_unsaturated_solinas_scmul_spec.
  Proof. scmul_spec_from_ops reified_scmul121665 n s c. Defined.

  Local Instance curve25519_bedrock2_scmul121665_correctness :
    bedrock2_unsaturated_solinas_scmul_correctness.
  Proof. prove_correctness_scmul reified_scmul121665 n s c. Qed.
End Scmul121665.
