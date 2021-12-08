Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.

(* Parameters for Curve25519 field. *)
Section Field.
  Definition n : nat := 10.
  Definition s : Z := 2^255.
  Definition c : list (Z * Z) := [(1, 19)]%Z.

  Existing Instances Defaults32.default_parameters
           Defaults32.default_parameters_ok.
  Existing Instances no_select_size split_mul_to split_multiret_to.
  Definition prefix : string := "fe25519_"%string.

  (* Define Curve25519 field *)
  Instance field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos (UnsaturatedSolinas.m s c))) in
    (* curve 'A' parameter *)
    let a := constr:(F.of_Z M 486662) in
    let prefix := constr:("fe25519_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  (* Call fiat-crypto pipeline on all field operations *)
  Instance fe25519_ops : unsaturated_solinas_ops n s c.
  Proof using Type. Time constructor; make_computed_op. Defined.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

  Derive fe25519_from_bytes
         SuchThat (forall functions,
                      spec_of_from_bytes
                        (field_representation:=field_representation n s c)
                        (fe25519_from_bytes :: functions))
         As fe25519_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive fe25519_to_bytes
         SuchThat (forall functions,
                      spec_of_to_bytes
                        (field_representation:=field_representation n s c)
                        (fe25519_to_bytes :: functions))
         As fe25519_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive fe25519_mul
         SuchThat (forall functions,
                      spec_of_BinOp bin_mul
                        (field_representation:=field_representation n s c)
                        (fe25519_mul :: functions))
         As fe25519_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive fe25519_square
         SuchThat (forall functions,
                      spec_of_UnOp un_square
                        (field_representation:=field_representation n s c)
                        (fe25519_square :: functions))
         As fe25519_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive fe25519_add
         SuchThat (forall functions,
                      spec_of_BinOp bin_add
                        (field_representation:=field_representation n s c)
                        (fe25519_add :: functions))
         As fe25519_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive fe25519_sub
         SuchThat (forall functions,
                      spec_of_BinOp bin_sub
                        (field_representation:=field_representation n s c)
                        (fe25519_sub :: functions))
         As fe25519_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  Derive fe25519_scmula24
         SuchThat (forall functions,
                      spec_of_UnOp un_scmula24
                        (field_representation:=field_representation n s c)
                        (fe25519_scmula24 :: functions))
         As fe25519_scmula24_correct.
  Proof. Time derive_bedrock2_func scmula24_op. Qed.
End Field.

(* Uncomment below to sanity-check that compilation works *)
(*
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compilerExamples.MMIO.

Definition funcs : list func :=
  [ fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_to_bytes;
    fe25519_from_bytes ].

Compute compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list funcs).
*)
