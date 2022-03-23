Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Local Open Scope string_scope.
Import ListNotations.


Derive ladderstep SuchThat
       (ladderstep = ladderstep_body
                       (BW:=BW32)
                       (field_parameters:=field_parameters)
                       (field_representaton:=field_representation n s c))
       As ladderstep_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Derive montladder SuchThat
       (montladder
        = montladder_body
            (BW:=BW32)
            (Z.to_nat (Z.log2_up Curve25519.l))
            (field_parameters:=field_parameters)
            (field_representaton:=field_representation n s c))
       As montladder_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Definition funcs : list func :=
  [
    montladder;
    fe25519_to_bytes;
    fe25519_from_bytes;
    fe25519_from_word;
    CSwap.cswap_body(word:=BasicC32Semantics.word)(field_parameters:=field_parameters)(field_representaton:=field_representation n s c);
    fe25519_copy;
    fe25519_inv(word:=BasicC32Semantics.word)(field_parameters:=field_parameters);
    ladderstep;
    fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_scmula24 ].

(*
Require Import bedrock2.ToCString.
Compute c_module funcs.
*)

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         (map.of_list funcs) = Success montladder_compiler_result)
       As montladder_compiler_result_ok.
Proof.
  vm_compute. apply f_equal. subst; exact eq_refl.
Qed.
