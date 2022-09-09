Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.Symbols.
Require Import compiler.MMIO.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Local Open Scope string_scope.
Import ListNotations.

Local Instance frep25519 : Field.FieldRepresentation(field_parameters:=field_parameters) := field_representation n Field25519.s c.
Derive ladderstep SuchThat (ladderstep = ladderstep_body) As ladderstep_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Derive montladder SuchThat (montladder = montladder_body (Z.to_nat (Z.log2 Curve25519.order)))
       As montladder_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Require Import bedrock2.NotationsCustomEntry.

Definition x25519 : func := ("x25519", (["out"; "sk"; "pk"], [], bedrock_func_body:(
  stackalloc 40 as U;
  fe25519_from_bytes(U, pk);
  stackalloc 40 as OUT;
  montladder(OUT, sk, U);
  fe25519_to_bytes(out, OUT)
))).

Definition x25519_base : func := ("x25519_base", (["out"; "sk"], [], bedrock_func_body:(
  stackalloc 40 as U;
  fe25519_from_word(U, $9);
  stackalloc 40 as OUT;
  montladder(OUT, sk, U);
  fe25519_to_bytes(out, OUT)
))).

Import LittleEndianList.
Local Coercion F.to_Z : F >-> Z.
Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Syntax bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.OfListWord Coq.Init.Byte coqutil.Byte.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
Definition x25519_gallina := montladder_gallina (Field.M_pos(FieldParameters:=field_parameters)) Field.a24 (Z.to_nat (Z.log2 (Z.pos order))).
Global Instance spec_of_x25519 : spec_of x25519 :=
  fnspec! "x25519" out sk pk / (o s p : list Byte.byte) (R : _ -> Prop),
  { requires t m := m =* s$@sk * p$@pk * o$@out * R /\
      length s = 32%nat /\ length p = 32%nat /\ length o = 32%nat /\ byte.unsigned (nth 31 p x00) <= 0x7f;
    ensures t' m := t=t' /\ m=* s$@sk ⋆ p$@pk ⋆ R ⋆
      (le_split 32 (x25519_gallina (le_combine s) (Field.feval_bytes p)))$@out }.

Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.
Local Instance spec_of_fe25519_from_bytes : spec_of "fe25519_from_bytes" := Field.spec_of_from_bytes.
Local Instance spec_of_fe25519_to_bytes : spec_of "fe25519_to_bytes" := Field.spec_of_to_bytes.
Local Instance spec_of_montladder : spec_of "montladder" := spec_of_montladder(Z.to_nat (Z.log2 Curve25519.order)).

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.
Lemma x25519_ok : program_logic_goal_for_function! x25519.
Proof.
  repeat straightline.
  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H2. { transitivity 40%nat; trivial. }

  straightline_call; ssplit.
  { eexists. ecancel_assumption. }
  { cbv [Field.FElem].
    use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 0%nat; cbn; trivial. eapply RelationClasses.reflexivity. }
  { unfold Field.bytes_in_bounds, frep25519, field_representation, Signature.field_representation, Representation.frep.
    match goal with |- ?P ?x ?z => let y := eval cbv in x in change (P y z) end; cbn.
    repeat (destruct p as [|? p]; try (cbn [length] in *;discriminate); []).
    cbn; cbn [nth] in *.
    cbv [COperationSpecifications.list_Z_bounded_by FoldBool.fold_andb_map map seq]; cbn.
    pose proof byte.unsigned_range as HH. setoid_rewrite <-Le.Z.le_sub_1_iff in HH. cbn in HH.
    setoid_rewrite Zle_is_le_bool in HH. setoid_rewrite <-Bool.andb_true_iff in HH.
    rewrite 31HH; cbn.
    eapply Bool.andb_true_iff; split; trivial.
    eapply Bool.andb_true_iff; split; eapply Zle_is_le_bool; trivial.
    eapply byte.unsigned_range. }
  repeat straightline.

  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a2) H15. { transitivity 40%nat; trivial. }

  straightline_call; ssplit.
  3: { unfold FElem, Field.FElem in *; extract_ex1_and_emp_in_goal; ssplit.
       { use_sep_assumption. cancel; repeat ecancel_step.
       cancel_seps_at_indices 0%nat 0%nat; trivial. cbn; reflexivity. }
    all : eauto.
    { instantiate (1:=None). exact I. } }
  { reflexivity. }
  { rewrite H3. vm_compute. inversion 1. }
  repeat straightline.

  cbv [FElem] in H22. extract_ex1_and_emp_in H22.
  straightline_call; ssplit.
  { ecancel_assumption. }
  { transitivity 32%nat; auto. }
  { eexists. ecancel_assumption. }
  { intuition idtac. }
  repeat straightline_cleanup.
  repeat straightline.

  cbv [Field.FElem] in *.
  seprewrite_in @Bignum.Bignum_to_bytes H25.
  seprewrite_in @Bignum.Bignum_to_bytes H25.
  extract_ex1_and_emp_in H25.

  repeat straightline; intuition eauto.
  rewrite H29 in *. cbv [x25519_gallina].
  use_sep_assumption; cancel. eapply RelationClasses.reflexivity.
Qed.

Global Instance spec_of_x25519_base : spec_of x25519_base :=
  fnspec! "x25519_base" out sk / (o s : list Byte.byte) (R : _ -> Prop),
  { requires t m := m =* s$@sk * o$@out * R /\
      length s = 32%nat /\ length o = 32%nat;
    ensures t' m := t=t' /\ m=* s$@sk ⋆ R ⋆
      (le_split 32 (x25519_gallina (le_combine s) (F.of_Z _ 9)))$@out }.

Lemma x25519_base_ok : program_logic_goal_for_function! x25519_base.
Proof.
  repeat straightline.
  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H2. { transitivity 40%nat; trivial. }
  straightline_call; ssplit.
  { cbv [Field.FElem]. cbn. cbv [n]. ecancel_assumption. }
  repeat straightline.

  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a2) H13. { transitivity 40%nat; trivial. }

  straightline_call; ssplit.
  3: { unfold FElem, Field.FElem in *; extract_ex1_and_emp_in_goal; ssplit.
       { use_sep_assumption. cancel; repeat ecancel_step.
       cancel_seps_at_indices 0%nat 0%nat; trivial. cbn; reflexivity. }
    all : eauto.
    { instantiate (1:=None). exact I. } }
  { reflexivity. }
  { rewrite H3. vm_compute. inversion 1. }
  repeat straightline.

  unfold FElem in H20. extract_ex1_and_emp_in H20.
  straightline_call; ssplit.
  { ecancel_assumption. }
  { transitivity 32%nat; auto. }
  { eexists. ecancel_assumption. }
  { intuition idtac. }
  repeat straightline_cleanup.
  repeat straightline.

  cbv [Field.FElem] in *.
  seprewrite_in @Bignum.Bignum_to_bytes H23.
  seprewrite_in @Bignum.Bignum_to_bytes H23.
  extract_ex1_and_emp_in H23.

  repeat straightline; intuition eauto.
  rewrite H27 in *. cbv [x25519_gallina].
  use_sep_assumption; cancel. eapply RelationClasses.reflexivity.
Qed.

Require Import coqutil.Word.Naive.

Definition funcs : list func :=
  [ x25519; x25519_base;
    montladder;
    fe25519_to_bytes;
    fe25519_from_bytes;
    fe25519_from_word;
    CSwap.cswap_body(word:=word32)(field_parameters:=field_parameters)(field_representaton:=field_representation n s c);
    fe25519_copy;
    fe25519_inv(word:=word32)(field_parameters:=field_parameters);
    ladderstep;
    fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_scmula24 ].


Definition montladder_c_module := ToCString.c_module funcs.

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         funcs = Success montladder_compiler_result)
       As montladder_compiler_result_ok.
Proof.
  match goal with x := _ |- _ => cbv delta [x]; clear x end.
  vm_compute.
  match goal with |- @Success ?A ?x = Success ?e => is_evar e;
    exact (@eq_refl (result A) (@Success A x)) end.
Qed.

Definition montladder_stack_size := snd montladder_compiler_result.
Definition montladder_finfo := snd (fst montladder_compiler_result).
Definition montladder_insns := fst (fst montladder_compiler_result).
Definition montladder_bytes := Pipeline.instrencode montladder_insns.
Definition montladder_symbols : list byte := Symbols.symbols montladder_finfo.


Require riscv.Utility.InstructionNotations.
Require riscv.Utility.InstructionCoercions.
Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Import riscv.Utility.InstructionCoercions.
  Unset Printing Coercions.

  (* Compute garagedoor_finfo. (* fe25519_mul is more than 10KB in just one function *) *)
  Goal True. let r := eval cbv in montladder_insns in idtac (* r *). Abort.
End PrintAssembly.
