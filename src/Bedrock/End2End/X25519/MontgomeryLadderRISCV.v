From Coq Require Import ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.
Require Import compiler.NaiveRiscvWordProperties.
Require Import coqutil.Map.SortedListWord.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.

Local Arguments map.rep: clear implicits.

#[export]
Instance BWM_RV32IM : FlatToRiscvCommon.bitwidth_iset 32 Decode.RV32IM := eq_refl.

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         funcs = Success montladder_compiler_result)
       As montladder_compiler_result_ok.
Proof.
  match goal with x := _ |- _ => cbv delta [x]; clear x end.
  match goal with |- ?a = _ => set a end.
  vm_compute.
  match goal with |- @Success ?A ?x = Success ?e => is_evar e;
    exact (@eq_refl (result A) (@Success A x)) end.
Qed.

Definition montladder_stack_size := snd montladder_compiler_result.
Definition montladder_finfo := snd (fst montladder_compiler_result).
Definition montladder_insns := fst (fst montladder_compiler_result).
Definition montladder_bytes := Pipeline.instrencode montladder_insns.
Definition montladder_symbols : list _ := Symbols.symbols montladder_finfo.

Require riscv.Utility.InstructionNotations.
Require riscv.Utility.InstructionCoercions.
Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Import riscv.Utility.InstructionCoercions.
  Unset Printing Coercions.

  (* Compute garagedoor_finfo. (* fe25519_mul is more than 10KB in just one function *) *)
  Goal True. let r := eval cbv in montladder_insns in idtac (* r *). Abort.
End PrintAssembly.

Definition f_rel_pos : Z := ltac:(
  let y := eval vm_compute in (List.find (fun '(name, pos) => String.eqb name "montladder") montladder_finfo) in
  match y with Some (_, ?pos) => exact pos end).

Local Instance mem : map.map (word.rep (width:=32)) Init.Byte.byte := SortedListWord.map _ _.
Local Existing Instance BW32.
