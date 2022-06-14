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
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.

Local Arguments map.rep: clear implicits.

Definition montladder_insns := fst (fst montladder_compiler_result).
Definition montladder_finfo := snd (fst montladder_compiler_result).
Definition montladder_stack_size := snd montladder_compiler_result.

Definition fname := fst montladder.
Definition argnames := fst (fst (snd montladder)).
Definition retnames := snd (fst (snd montladder)).
Definition fbody := snd (snd montladder).
Definition f_rel_pos : Z.
  let x := constr:(map.get montladder_finfo fname) in
  let y := eval vm_compute in x in
  match y with
  | Some ?pos => exact pos
  end.
Defined.

Local Instance mem : map.map (word.rep (width:=32)) Init.Byte.byte := SortedListWord.map _ _.
Local Existing Instance BW32.

(* Postcondition extracted from spec_of_montladder *)
Definition montladder_post (pOUT pK pU : word.rep (word:=BasicC32Semantics.word))
          (Kbytes : list Byte.byte) (K : Z)
          (U : F (Field.M_pos (FieldParameters:=field_parameters)))
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
         (montladder_gallina Field.M_pos Field.a24 (Z.to_nat (Z.log2_up Curve25519.l)) K U)
         ⋆ Array.array ptsto (word.of_Z 1) pK Kbytes
         ⋆ FElem (BW:=BW32)
                 (field_representaton:=field_representation n s c)
                 (Some Field.tight_bounds) pU U ⋆ R)%sep
        mem').

Local Instance Registers : map.map Z (@word.rep 32 BasicC32Semantics.word)
  := Zkeyed_map _.

Require Import riscv.Spec.Decode.

Local Existing Instance RV32I_bitwidth.

(* TODO: does something like this already exist? *)
(* when the function name being called is not first in the list of functions,
   peel off non-matching names *)
Local Ltac prepare_call_step :=
  lazymatch goal with
  | |- ?call (?f :: ?funcs) ?fname ?t ?m ?args ?post =>
    assert_fails (unify (fst f) fname);
    let H := fresh in
    assert (call funcs fname t m args post) as H;
    [ | remember funcs; rewrite (surjective_pairing f);
        cbn [WeakestPrecondition.call WeakestPrecondition.call_body ];
        lazymatch goal with |- context[if (String.eqb ?x ?y) then _ else _] =>
          let x' := (eval vm_compute in x) in change x with x';
          let y' := (eval vm_compute in y) in change y with y';
          destr (String.eqb x' y'); [ congruence | ]
        end; exact H ]
  end.
Local Ltac prepare_call := repeat prepare_call_step.

(* TODO: move to Spec.Field? *)
Section Generic.
  Context {width : Z} {BW : Bitwidth width} {word : word width}
          {mem : map.map word.rep (Init.Byte.byte : Type)}
          {locals : map.map string (word.rep (word:=word))}
          {ext_spec : Semantics.ExtSpec}
          {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.

  Lemma peel_func_binop
      {name} (op : BinOp name) funcs0 funcs :
    fst funcs0 <> name ->
    spec_of_BinOp op funcs ->
    spec_of_BinOp op (funcs0 :: funcs).
  Proof.
    cbv [spec_of_BinOp binop_spec]; intros.
    cbn [WeakestPrecondition.call WeakestPrecondition.call_body ].
    destruct funcs0; cbn [fst snd] in *.
    lazymatch goal with |- context[if (String.eqb ?x ?y) then _ else _] =>
      destr (String.eqb x y); [ congruence | ]
    end.
    eauto.
  Qed.

  Lemma peel_func_unop
      {name} (op : UnOp name) funcs0 funcs :
    fst funcs0 <> name ->
    spec_of_UnOp op funcs ->
    spec_of_UnOp op (funcs0 :: funcs).
  Proof.
    cbv [spec_of_UnOp unop_spec]; intros.
    cbn [WeakestPrecondition.call WeakestPrecondition.call_body ].
    destruct funcs0; cbn [fst snd] in *.
    lazymatch goal with |- context[if (String.eqb ?x ?y) then _ else _] =>
      destr (String.eqb x y); [ congruence | ]
    end.
    eauto.
  Qed.

End Generic.

Lemma valid_funs_funcs : ExprImp.valid_funs (map.of_list funcs).
Proof.
  unfold ExprImp.valid_funs. unfold funcs.
  (* TODO: need lemma/tactic to break down map.get (map.of_list [...]) into a
     case for each function, then valid_fun is just proving there are no
     duplicates in arg/ret names *)
Admitted.

Local Instance naive_word_riscv_ok :
  RiscvWordProperties.word.riscv_ok BasicC32Semantics.word := naive_word_riscv_ok 5.

Lemma weaken_bounded_by :
forall X : list Z,
COperationSpecifications.list_Z_bounded_by
  (UnsaturatedSolinasHeuristics.tight_bounds n s c) X ->
COperationSpecifications.list_Z_bounded_by
  (UnsaturatedSolinasHeuristics.loose_bounds n s c) X.
Admitted.

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
    with (fname:=fname).
  all:cbn [fname montladder fst snd].

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
      | |- map.get montladder_finfo _ = Some _ => reflexivity
      | _ => idtac
      end.

  (* solve remaining goals one by one *)
  { eapply (compile_ext_call_correct (funname_env_ok:=SortedListString.ok)). }
  { intros. cbv [compile_ext_call compile_interact].
    repeat (destruct_one_match; try reflexivity). }
  { apply valid_funs_funcs. }
  { lazy. repeat constructor; cbn [In]; intuition idtac; congruence. }
  { unfold funcs.
    (* montladder is not at the front of the function list; remove everything
       that doesn't match the name *)
    prepare_call.
    (* use montladder correctness proof *)
    rewrite montladder_defn.
    eapply @montladder_correct; try (typeclasses eauto).
    { apply Signature.field_representation_ok.
      apply UnsaturatedSolinas.relax_valid. }
    { reflexivity. }
    { cbv [Core.__rupicola_program_marker]. tauto. }
    { exact I. }
    { eapply CSwap.cswap_body_correct; [|exact I].
      unfold field_representation, Signature.field_representation, Representation.frep; cbn; unfold n; cbv; trivial. }
    { eapply fe25519_copy_correct. }
    { eapply fe25519_from_word_correct. }
    {
      cbv [LadderStep.spec_of_ladderstep]; intros.
      prepare_call. rewrite ladderstep_defn.
      eapply @LadderStep.ladderstep_correct; try (typeclasses eauto).
      { apply Signature.field_representation_ok.
        apply UnsaturatedSolinas.relax_valid. }
      { cbv [Core.__rupicola_program_marker]; tauto. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_mul_correct. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_add_correct. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_sub_correct. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_square_correct. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_scmula24_correct. }
      { ecancel_assumption. } }
    { repeat (apply peel_func_unop; [ lazy; congruence | ]).
      unshelve eapply AdditionChains.fe25519_inv_correct_exp; try exact I.
      { unshelve eapply Signature.field_representation_ok, weaken_bounded_by. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_square_correct. }
      { repeat (apply peel_func_binop; [ lazy; congruence | ]).
        apply fe25519_mul_correct. } }
    { repeat (apply peel_func_unop; [ lazy; congruence | ]).
      apply fe25519_mul_correct. }
    { ssplit; try eassumption; [ ].
      lazymatch goal with H : length Kbytes = _ |- _ => rewrite H end.
      lazy; congruence. } }
  { assumption. }
  { assumption. }
  { assumption. }
Qed.

(* Print Assumptions montladder_compiles_correctly. *)
