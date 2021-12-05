Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Local Open Scope string_scope.
Import ListNotations.

Definition ladderstep : func :=
  Eval vm_compute in
    (ladderstep_body
      (field_parameters:=field_parameters)
      (field_representaton:=field_representation n s c)).

Definition montladder : func :=
  Eval vm_compute in
    (montladder_body (Z.to_nat (Z.log2_up Curve25519.l))
      (field_parameters:=field_parameters)
      (field_representaton:=field_representation n s c)).

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

Definition compiler_test_out := Eval vm_compute in
  compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list funcs).
Compute
  match compiler_test_out with
  Success ((x, z), y) => Success (length x, z) | Failure e => Failure e end.

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         (map.of_list funcs) = Some montladder_compiler_result)
       As montladder_compiler_result_ok.
Proof.
  vm_compute. apply f_equal. subst; exact eq_refl.
Qed.

Check montladder_correct.

Check compiler_correct.

Local Arguments map.rep: clear implicits.
Check montladder_compiler_result.

Let montladder_insns := fst (fst montladder_compiler_result).
Let montladder_finfo := snd (fst montladder_compiler_result).
Let montladder_stack_size := snd montladder_compiler_result.

Let fname := fst montladder.
Let argnames := fst (fst (snd montladder)).
Let retnames := snd (fst (snd montladder)).
Let fbody := snd (snd montladder).
Definition f_rel_pos : Z.
  let x := constr:(map.get montladder_finfo fname) in
  let y := eval vm_compute in x in
  match y with
  | Some (_, ?pos) => exact pos
  end.
Defined.

Require Import coqutil.Map.SortedListWord.

Require Import bedrock2.Map.Separation.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.

Local Instance mem : map.map (word.rep (width:=32)) Init.Byte.byte := SortedListWord.map _ _.
Local Existing Instance BW32.


(* scalars are 253 bits = 8 words *)
Definition scalar_size_in_words := 8%nat.

(* A scalar is represented as a (saturated, little-endian) array of words *)
Definition eval_scalar_words (ws : list word.rep) : Z :=
  Positional.eval (ModOps.weight 32 1) scalar_size_in_words
                  (List.map (word.unsigned (word:=BasicC32Semantics.word)) ws).


Local Instance scalar_representation : ScalarRepresentation :=
  {| scalar := list word.rep;
     sceval := fun ws =>  F.of_Z _ (eval_scalar_words ws);
     Scalar := Bignum.Bignum scalar_size_in_words;
  |}.


Print spec_of_montladder.
Check (
  compiler_correct compile_ext_call compile_ext_call_correct _ (map.of_list funcs)
                   montladder_insns montladder_finfo montladder_stack_size
                   fname argnames retnames fbody 
).


Definition foo := fun post =>
         (forall (pOUT pK pU : word.rep)
                 (K : scalar) (U : F Field.M_pos)
                 (out_bound : option Field.bounds) (OUT : F Field.M_pos)
                 (R : map.rep _ _ mem -> Prop) 
                 (tr : Semantics.trace)
                 (mem0 : map.rep _ _ mem),
           (FElem (field_parameters:=field_parameters)
                  (field_representaton:=field_representation n s c)
                  (BW:=BW32)
                  out_bound pOUT OUT
            ⋆ Scalar (scalar_field_parameters:=scalar_field_parameters)
                     (ScalarRepresentation:=scalar_representation)
                     (BW:=BW32)
                     pK K
            ⋆ FElem (field_parameters:=field_parameters)
                    (field_representaton:=field_representation n s c)
                    (BW:=BW32)
                   (Some Field.tight_bounds) pU U ⋆ R)%sep mem0 ->
           WeakestPrecondition.call funcs fname tr mem0 
             [pOUT; pK; pU] post).


Print spec_of_montladder.


(* Postcondition extracted from spec_of_montladder *)
Definition montladder_post (pOUT pK pU : word.rep (word:=BasicC32Semantics.word))
          (K : scalar (scalar_field_parameters:=scalar_field_parameters)) 
          (U : F (Field.M_pos (FieldParameters:=field_parameters)))
          (out_bound : option (Field.bounds (BW:=BW32) (word:=BasicC32Semantics.word)
                                            (mem:=mem)
                                            (field_parameters:=field_parameters)
                                            (FieldRepresentation:=field_representation n s c)))
          (OUT : F (Field.M_pos (FieldParameters:=field_parameters)))
          (R : map.rep word.rep Init.Byte.byte mem -> Prop)
          (tr : Semantics.trace) : 
  Semantics.trace -> map.rep _ _ mem -> list (word.rep (word:=BasicC32Semantics.word)) -> Prop :=
   (fun (tr' : Semantics.trace)
        (mem' : map.rep word.rep Init.Byte.byte mem)
        (rets : list word.rep) =>
      rets = [] /\
      tr' = tr /\
      (FElem
         (BW:=BW32)
         (field_representaton:=field_representation n s c)
         (Some Field.tight_bounds) pOUT
         (montladder_gallina scalarbits
            (fun i : nat => Z.testbit (F.to_Z (sceval K)) (Z.of_nat i))
            U)
         ⋆ Scalar pK K
         ⋆ FElem (BW:=BW32)
                 (field_representaton:=field_representation n s c)
                 (Some Field.tight_bounds) pU U ⋆ R)%sep
        mem').


(* TODO: next, plug in specific pOUT, pK, etc for argvals and add their preconditions from spec_of_montladder *)
Lemma montladder_compiles_correctly :
  forall (t : Semantics.trace)
         (mH : map.rep word.rep Init.Byte.byte mem)
         (argvals : list word.rep)
         (initial : MetricRiscvMachine)
         (stack_lo stack_hi ret_addr p_funcs : word.rep)
         (Rdata Rexec : map.rep word.rep Init.Byte.byte mem -> Prop),
         montladder_stack_size <=
         word.unsigned (word.sub stack_hi stack_lo) /
         SeparationLogic.bytes_per_word ->
         word.unsigned (word.sub stack_hi stack_lo)
         mod SeparationLogic.bytes_per_word = 0 ->
         getPc (getMachine initial) = word.add p_funcs (word.of_Z f_rel_pos) ->
         map.get (getRegs (getMachine initial)) RegisterNames.ra =
         Some ret_addr ->
         word.unsigned ret_addr mod 4 = 0 ->
         map.getmany_of_list (getRegs (getMachine initial))
           (firstn (Datatypes.length argnames) (reg_class.all reg_class.arg)) =
         Some argvals ->
         getLog (getMachine initial) = t ->
         LowerPipeline.machine_ok p_funcs stack_lo stack_hi montladder_insns
           mH Rdata Rexec initial ->
         FlatToRiscvCommon.runsTo initial
           (fun final : MetricRiscvMachine =>
            exists
              (mH' : map.rep word.rep Init.Byte.byte mem) 
            (retvals : list word.rep),
              map.getmany_of_list (getRegs (getMachine final))
                (firstn (Datatypes.length retnames)
                   (reg_class.all reg_class.arg)) = 
              Some retvals /\
              ?post (getLog (getMachine final)) mH' retvals /\
              map.agree_on LowerPipeline.callee_saved
                (getRegs (getMachine initial)) (getRegs (getMachine final)) /\
              getPc (getMachine final) = ret_addr /\
              LowerPipeline.machine_ok p_funcs stack_lo stack_hi
                montladder_insns mH' Rdata Rexec final).


Check (
  compiler_correct compile_ext_call compile_ext_call_correct _ (map.of_list funcs)
                   montladder_insns montladder_finfo montladder_stack_size
                   fname argnames retnames fbody _ _ _ _ _ _ _
     _
).
