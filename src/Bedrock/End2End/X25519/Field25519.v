Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults32.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.

Existing Instances BW32.
Existing Instances no_select_size split_mul_to split_multiret_to.

(* Parameters for Curve25519 field (32-bit machine). *)
Section Field.
  Context {ext_spec: Semantics.ExtSpec} {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Definition n : nat := 10.
  Definition s : Z := 2^255.
  Definition c : list (Z * Z) := [(1, 19)]%Z.

  Definition prefix : string := "fe25519_"%string.

  (* Note: Cannot use Defaults32.default_parameters here as the parameters for
     the bedrock2 backend because it uses BasicC32Semantics.ext_spec, while we
     will eventually want to plug in FE310CSemantics.ext_spec. TODO: is there a
     way to prove the ext_spec doesn't matter here, since we're not using any MMIO? *)
  (* Parameters for the fiat-crypto bedrock2 backend *)
  Instance translation_parameters : Types.parameters
    (word := BasicC32Semantics.word)
    (varname_gen := default_varname_gen)
    (error := Syntax.expr.var Defaults.ERROR)
    := tt.
  Instance translation_parameters_ok : Types.ok.
  Proof. constructor; try exact _; apply prefix_name_gen_unique. Qed.

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
  Instance fe25519_ops : unsaturated_solinas_ops (ext_spec:=ext_spec) n s c.
  Proof using Type. Time constructor; make_computed_op. Defined.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

  Derive fe25519_from_bytes
         SuchThat (forall functions,
                      spec_of_from_bytes
                        (ext_spec:=ext_spec)
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

  Derive fe25519_copy
         SuchThat (forall functions,
                      spec_of_felem_copy
                        (field_representation:=field_representation n s c)
                        (fe25519_copy :: functions))
         As fe25519_copy_correct.
  Proof. Time derive_bedrock2_func felem_copy_op. Qed.

  Derive fe25519_from_word
         SuchThat (forall functions,
                      spec_of_from_word
                        (field_representation:=field_representation n s c)
                        (fe25519_from_word :: functions))
         As fe25519_from_word_correct.
  Proof. Time derive_bedrock2_func from_word_op. Qed.

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
