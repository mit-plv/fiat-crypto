Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Local Open Scope Z_scope.
Import ListNotations.

Let n := 5%nat.
Let s := 2^130.
Let c := [(1, 5)].
Let machine_wordsize := 32.
Let prefix := "poly1305_"%string.

Instance names : names_of_operations.
make_names_of_operations prefix. Defined.

Instance p : Types.parameters.
make_parameters machine_wordsize. Defined.
Instance p_ok : Types.ok. typeclasses eauto. Qed.

Instance poly1305_bedrock2 : bedrock2_unsaturated_solinas n s c.
Proof. make_bedrock2_unsaturated_solinas. Time Defined.
