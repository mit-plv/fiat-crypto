Require Import Coq.ZArith.ZArith.
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
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.

Local Arguments map.rep: clear implicits.

Definition f_rel_pos : Z := ltac:(
  let y := eval vm_compute in (List.find (fun '(name, pos) => String.eqb name "montladder") montladder_finfo) in
  match y with Some (_, ?pos) => exact pos end).

Local Instance mem : map.map (word.rep (width:=32)) Init.Byte.byte := SortedListWord.map _ _.
Local Existing Instance BW32.

(* Postcondition extracted from spec_of_montladder *)
Definition montladder_post (pOUT pK pU : word.rep (word:=Naive.word32))
          (Kbytes : list Byte.byte) (K : Z)
          (U : F (Field.M_pos (FieldParameters:=field_parameters)))
          (OUT : F (Field.M_pos (FieldParameters:=field_parameters)))
          (R : map.rep word.rep Init.Byte.byte mem -> Prop)
          (tr : Semantics.trace) :
  Semantics.trace -> map.rep _ _ mem -> list (word.rep (word:=Naive.word32)) -> Prop :=
   (fun (tr' : Semantics.trace)
        (mem' : map.rep word.rep Init.Byte.byte mem)
        (rets : list word.rep) =>
      rets = [] /\
      tr' = tr /\
      (FElem
         (BW:=BW32)
         (field_representaton:=field_representation n s c)
         (Some Field.tight_bounds) pOUT
         (montladder_gallina Field.M_pos Field.a24 (Z.to_nat (Z.log2 Curve25519.order)) K U)
         ⋆ Array.array ptsto (word.of_Z 1) pK Kbytes
         ⋆ FElem (BW:=BW32)
                 (field_representaton:=field_representation n s c)
                 (Some Field.tight_bounds) pU U ⋆ R)%sep
        mem').

Local Instance Registers : map.map Z (@word.rep 32 Naive.word32)
  := Zkeyed_map _.

Require Import riscv.Spec.Decode.

Local Instance naive_word_riscv_ok :
  RiscvWordProperties.word.riscv_ok Naive.word32 := naive_word_riscv_ok 5.

Lemma link_montladder : spec_of_montladder (map.of_list funcs).
Proof.
    unfold spec_of_montladder, ScalarMult.MontgomeryLadder.spec_of_montladder.
    unfold funcs.
    (* use montladder correctness proof *)
    rewrite montladder_defn.
    eapply @montladder_correct; try (typeclasses eauto).
    { reflexivity. }
    { cbv [Core.__rupicola_program_marker]. tauto. }
    { exact I. }
    { reflexivity. }
    { eapply CSwap.cswap_body_correct; [|exact I|reflexivity].
      unfold field_representation, Signature.field_representation, Representation.frep; cbn; unfold n; cbv; trivial. }
    { eapply fe25519_copy_correct. reflexivity. }
    { eapply fe25519_from_word_correct. reflexivity. }
    {
      cbv [LadderStep.spec_of_ladderstep]; intros.
      rewrite ladderstep_defn.
      eapply @LadderStep.ladderstep_correct; try (typeclasses eauto).
      { cbv [Core.__rupicola_program_marker]; tauto. }
      { reflexivity. }
      { apply fe25519_mul_correct. reflexivity. }
      { apply fe25519_add_correct. reflexivity. }
      { apply fe25519_sub_correct. reflexivity. }
      { apply fe25519_square_correct. reflexivity. }
      { apply fe25519_scmula24_correct. reflexivity. }
      { ecancel_assumption. } }
    { unshelve eapply AdditionChains.fe25519_inv_correct_exp; [exact I|reflexivity| | ].
      { apply fe25519_square_correct. reflexivity. }
      { apply fe25519_mul_correct. reflexivity. } }
    { apply fe25519_mul_correct. reflexivity. }
Qed.

Lemma montladder_compiles_correctly :
  forall (t : Semantics.trace)
         (mH : map.rep word.rep Init.Byte.byte mem)
         (pOUT pK pU : word.rep) (out_bound : option Field.bounds)
         (OUT U: F Field.M_pos) (Kbytes : list Byte.byte) (K : Z)
         (initial : MetricRiscvMachine)
         (stack_lo stack_hi ret_addr p_funcs : word.rep)
         (R Rdata Rexec : map.rep word.rep Init.Byte.byte mem -> Prop),
         LittleEndianList.le_combine Kbytes = K ->
         length Kbytes = 32%nat ->
         (FElem (BW:=BW32)
                (field_representaton:=field_representation n s c)
                out_bound pOUT OUT
          ⋆ Array.array ptsto (word.of_Z 1) pK Kbytes
          ⋆  FElem (BW:=BW32)
                   (field_representaton:=field_representation n s c)
                   (Some Field.tight_bounds) pU U
          ⋆ R)%sep mH ->
         montladder_stack_size <=
         word.unsigned (word.sub stack_hi stack_lo) /
         SeparationLogic.bytes_per_word ->
         word.unsigned (word.sub stack_hi stack_lo)
         mod SeparationLogic.bytes_per_word = 0 ->
         getPc (getMachine initial) = word.add p_funcs (word.of_Z f_rel_pos) ->
         map.get (getRegs (getMachine initial)) RegisterNames.ra =
         Some ret_addr ->
         word.unsigned ret_addr mod 4 = 0 ->
         LowerPipeline.arg_regs_contain (getRegs (getMachine initial)) [pOUT; pK; pU] ->
         getLog (getMachine initial) = t ->
         LowerPipeline.machine_ok p_funcs stack_lo stack_hi montladder_insns
           mH Rdata Rexec initial ->
         FlatToRiscvCommon.runsTo initial
           (fun final : MetricRiscvMachine =>
            exists
              (mH' : map.rep word.rep Init.Byte.byte mem)
            (retvals : list word.rep),
              LowerPipeline.arg_regs_contain (getRegs (getMachine final)) retvals /\
              montladder_post pOUT pK pU Kbytes K U OUT R t
                 (getLog (getMachine final)) mH' retvals /\
              map.only_differ (getRegs (getMachine initial))
                              reg_class.caller_saved
                              (getRegs (getMachine final)) /\
              getPc (getMachine final) = ret_addr /\
              LowerPipeline.machine_ok p_funcs stack_lo stack_hi
                montladder_insns mH' Rdata Rexec final).
Proof.
  intros.
  eapply (compiler_correct_wp
            (ext_spec:=FE310CSemantics.ext_spec)
            (string_keyed_map := SortedListString.map)
            (string_keyed_map_ok := SortedListString.ok))
    with (fname:="montladder"%string).
  all:cbn [montladder fst snd].

  (* fill in easy subgoals that instantiate evars *)
  all:lazymatch goal with
      | |- compile _ _ = Success _ =>
        rewrite montladder_compiler_result_ok;
        transitivity (Success (montladder_insns,
                               montladder_finfo,
                               montladder_stack_size));
        [ | reflexivity ]; reflexivity
      | _ => idtac
      end.
  all:lazymatch goal with
      | |- getPc (getMachine _) = _ => eassumption
      | |- getLog (getMachine _) = _ => eassumption
      | |- map.get (getRegs (getMachine _)) _ = Some _ => eassumption
      | |- LowerPipeline.arg_regs_contain _ _ => eassumption
      | |- context [LowerPipeline.machine_ok] => eassumption
      | |- map.get _ "montladder"%string = Some _ => reflexivity
      | _ => idtac
      end.

  (* solve remaining goals one by one *)
  { eapply (compile_ext_call_correct (funname_env_ok:=SortedListString.ok)). }
  { intros. cbv [compile_ext_call compile_interact].
    repeat (destruct_one_match; try reflexivity). }
  { vm_compute. reflexivity. }
  { lazy. repeat constructor; cbn [In]; intuition idtac; congruence. }
  { eapply link_montladder.
    ssplit; try eassumption; [ ].
    lazymatch goal with H : length Kbytes = _ |- _ => rewrite H end.
    lazy; congruence. }
  { assumption. }
  { assumption. }
  { assumption. }
Qed.

(* Print Assumptions montladder_compiles_correctly. *)
