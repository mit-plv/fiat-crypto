Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Let n := 10%nat.
Let s := 2^255.
Let c := [(1, 19)].
Let machine_wordsize := 64.
Let prefix := "curve25519_"%string. (* placed before function names *)

Instance names : names_of_operations.
make_names_of_operations prefix. Defined.

Instance p : Types.parameters.
make_parameters machine_wordsize. Defined.
Instance p_ok : Types.ok. typeclasses eauto. Qed.

Instance curve25519_bedrock2_scmul
  : bedrock2_unsaturated_solinas_scmul n s c 121666.
Proof. make_bedrock2_unsaturated_solinas_scmul. Defined.

Instance curve25519_bedrock2 : bedrock2_unsaturated_solinas n s c.
Proof. make_bedrock2_unsaturated_solinas. Time Defined.
(* Eval cbv [carry_mul curve25519_bedrock2] in carry_mul. *)
