Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Parameters.SelectParameters.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Local Definition n := 10%nat.
Local Definition s := 2^255.
Local Definition c := [(1, 19)].
Local Definition machine_wordsize := 64.
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
Eval cbv [add curve25519_bedrock2] in add.
Eval cbv [spec_of_add curve25519_bedrock2] in spec_of_add.
*)

Section Scmul121666.
  Definition reified_scmul121666 :
    unsaturated_solinas_reified_scmul n s c machine_wordsize 121666.
  Proof. make_reified_scmul. Defined.

  Local Instance curve25519_bedrock2_scmul121666_func
    : bedrock2_unsaturated_solinas_scmul_func.
  scmul_func_from_ops reified_scmul121666. Defined.

  Local Instance curve25519_bedrock2_scmul121666_spec
    : bedrock2_unsaturated_solinas_scmul_spec.
  scmul_spec_from_ops reified_scmul121666 n s c. Defined.

  Local Instance curve25519_bedrock2_scmul121666_correctness :
    bedrock2_unsaturated_solinas_scmul_correctness.
  prove_correctness_scmul reified_scmul121666 n s c machine_wordsize.
  Defined.
End Scmul121666.

Section Scmul121665.
  Definition reified_scmul121665 :
    unsaturated_solinas_reified_scmul n s c machine_wordsize 121665.
  Proof. make_reified_scmul. Defined.

  Local Instance curve25519_bedrock2_scmul121665_func
    : bedrock2_unsaturated_solinas_scmul_func.
  scmul_func_from_ops reified_scmul121665. Defined.

  Local Instance curve25519_bedrock2_scmul121665_spec
    : bedrock2_unsaturated_solinas_scmul_spec.
  scmul_spec_from_ops reified_scmul121665 n s c. Defined.

  Local Instance curve25519_bedrock2_scmul121665_correctness :
    bedrock2_unsaturated_solinas_scmul_correctness.
  prove_correctness_scmul reified_scmul121665 n s c machine_wordsize.
  Defined.
End Scmul121665.
