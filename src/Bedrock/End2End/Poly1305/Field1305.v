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

(* Parameters for Poly1305 field. *)
Section Field.
  Definition n : nat := 5.
  Definition s : Z := 2^130.
  Definition c : list (Z * Z) := [(1, 5)]%Z.

  Existing Instances Defaults32.default_parameters
           Defaults32.default_parameters_ok.
  Definition prefix : string := "fe1305_"%string.

  (* Define Poly1305 field *)
  Instance field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos (UnsaturatedSolinas.m s c))) in
    (* dummy 'A' parameter since we don't care about scmula24 here *)
    let a := constr:(F.of_Z M 2) in
    let prefix := constr:("fe1305_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  (* Call fiat-crypto pipeline on all field operations *)
  Instance fe1305_ops : unsaturated_solinas_ops n s c.
  Proof using Type. Time constructor; make_computed_op. Defined.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

  Local Notation functions_contain functions f :=
    (Interface.map.get functions (fst f) = Some (snd f)).

  Derive fe1305_from_bytes
         SuchThat (forall functions,
                      functions_contain functions fe1305_from_bytes ->
                      spec_of_from_bytes
                        (field_representation:=field_representation n s c)
                        functions)
         As fe1305_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive fe1305_to_bytes
         SuchThat (forall functions,
                      functions_contain functions fe1305_to_bytes ->
                      spec_of_to_bytes
                        (field_representation:=field_representation n s c)
                        functions)
         As fe1305_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive fe1305_mul
         SuchThat (forall functions,
                      functions_contain functions fe1305_mul ->
                      spec_of_BinOp bin_mul
                        (field_representation:=field_representation n s c)
                        functions)
         As fe1305_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive fe1305_square
         SuchThat (forall functions,
                      functions_contain functions fe1305_square ->
                      spec_of_UnOp un_square
                        (field_representation:=field_representation n s c)
                        functions)
         As fe1305_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive fe1305_add
         SuchThat (forall functions,
                      functions_contain functions fe1305_add ->
                      spec_of_BinOp bin_add
                        (field_representation:=field_representation n s c)
                        functions)
         As fe1305_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive fe1305_carry_add
         SuchThat (forall functions,
                      functions_contain functions fe1305_carry_add ->
                      spec_of_BinOp bin_carry_add
                        (field_representation:=field_representation n s c)
                        (functions))
         As fe1305_carry_add_correct.
  Proof. Time derive_bedrock2_func carry_add_op. Qed.

  Derive fe1305_sub
         SuchThat (forall functions,
                      functions_contain functions fe1305_sub ->
                      spec_of_BinOp bin_sub
                        (field_representation:=field_representation n s c)
                        functions)
         As fe1305_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.
End Field.

(* Uncomment below to sanity-check that compilation works *)
(*
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.

Definition funcs : list (string * func) :=
  [ fe1305_mul;
    fe1305_add;
    fe1305_carry_add;
    fe1305_sub;
    fe1305_square;
    fe1305_to_bytes;
    fe1305_from_bytes ].

#[local]
Instance BWM_RV32IM : FlatToRiscvCommon.bitwidth_iset 32 Decode.RV32IM := eq_refl.

Compute compile (compile_ext_call (funname_env:=SortedListString.map)) funcs.
*)
