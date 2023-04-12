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
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadder.
Require Import bedrock2Examples.LAN9250.
Require Import bedrock2Examples.lightbulb.
Require Import bedrock2Examples.memequal.
Require Import bedrock2Examples.memswap.
Require Import bedrock2Examples.memconst.
Require Import Rupicola.Examples.Net.IPChecksum.IPChecksum.
Require Import Crypto.Bedrock.End2End.X25519.GarageDoor.
Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadderProperties.
Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry.
Import ListNotations.
Import Coq.Init.Byte.
Import coqutil.Macros.WithBaseName.
Import WeakestPrecondition ProgramLogic SeparationLogic.

(* these wrappers exist because CompilerInvariant requires execution proofs with arbitrary locals in the starting state, which ProgramLogic does not support *)
Definition init := func! { initfn() } .
Definition loop := func! { loopfn() } .
Definition memconst_pk := memconst garageowner.
Definition ip_checksum := ip_checksum_br2fn.

Definition funcs :=
  &[, init; loop;
    initfn; loopfn;
    memswap; memequal; memconst_pk;
    ip_checksum;
    ChaCha20.chacha20_block; ChaCha20.quarter;
    lan9250_tx ]
    ++lightbulb.function_impls
    ++MontgomeryLadder.funcs.

Lemma chacha20_ok: forall functions, ChaCha20.spec_of_chacha20 (&,ChaCha20.chacha20_block::&,ChaCha20.quarter::functions).
  intros.
  simple eapply ChaCha20.chacha20_block_body_correct.
  constructor.
  eapply ChaCha20.quarter_body_correct.
  constructor.
Qed.

Import SPI.
Lemma link_loopfn : spec_of_loopfn funcs.
Proof.
  eapply loopfn_ok; try eapply memswap.memswap_ok; try eapply memequal_ok.
    repeat (eapply recvEthernet_ok || eapply lightbulb_handle_ok);
        eapply lan9250_readword_ok; eapply spi_xchg_ok;
        (eapply spi_write_ok || eapply spi_read_ok).
    eapply ip_checksum_br2fn_ok; exact I.
    eapply x25519_base_ok; try eapply fe25519_from_word_correct; try eapply link_montladder; try eapply fe25519_to_bytes_correct.
    eapply lan9250_tx_ok; try eapply lan9250_writeword_ok; try eapply spi_xchg_ok; (eapply spi_write_ok || eapply spi_read_ok).
    eapply x25519_ok; try eapply fe25519_from_bytes_correct; try eapply link_montladder; try eapply fe25519_to_bytes_correct.
    eapply chacha20_ok.
Qed. Optimize Heap.

Require compiler.ToplevelLoop.
Definition ml: MemoryLayout.MemoryLayout(word:=Naive.word32) := {|
  MemoryLayout.code_start    := word.of_Z 0x20400000;
  MemoryLayout.code_pastend  := word.of_Z 0x21400000;
  MemoryLayout.heap_start    := word.of_Z 0x80000000;
  MemoryLayout.heap_pastend  := word.of_Z 0x80002000;
  MemoryLayout.stack_start   := word.of_Z 0x80002000;
  MemoryLayout.stack_pastend := word.of_Z 0x80004000;
|}.

Lemma ml_ok : MemoryLayout.MemoryLayoutOk ml. Proof. split; cbv; trivial; inversion 1. Qed.

Local Instance : FlatToRiscvCommon.bitwidth_iset 32 Decode.RV32IM := eq_refl.
Derive garagedoor_compiler_result SuchThat
  (ToplevelLoop.compile_prog (string_keyed_map:=@SortedListString.map) MMIO.compile_ext_call ml funcs
  = Success garagedoor_compiler_result)
  As garagedoor_compiler_result_ok.
Proof.
  match goal with x := _ |- _ => cbv delta [x]; clear x end.
  vm_compute.
  match goal with |- @Success ?A ?x = Success ?e => is_evar e;
    exact (@eq_refl (result A) (@Success A x)) end.
Qed. Optimize Heap.

Definition garagedoor_stack_size := snd garagedoor_compiler_result.
Definition garagedoor_finfo := snd (fst garagedoor_compiler_result).
Definition garagedoor_insns := fst (fst garagedoor_compiler_result).
Definition garagedoor_bytes := Pipeline.instrencode garagedoor_insns.
Definition garagedoor_symbols : list byte := Symbols.symbols garagedoor_finfo.

Require Import compiler.CompilerInvariant.
Require Import compiler.NaiveRiscvWordProperties.
Local Existing Instance SortedListString.map.
Import TracePredicate TracePredicateNotations SPI lightbulb_spec.
Import GarageDoor.

Lemma compiler_emitted_valid_instructions :
  bverify.bvalidInstructions Decode.RV32IM garagedoor_insns = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition good_trace s t s' :=
  exists ioh, SPI.mmio_trace_abstraction_relation ioh t /\
  (BootSeq +++ stateful garagedoor_iteration s s') ioh.
Import ExprImpEventLoopSpec.
Definition garagedoor_spec : ProgramSpec := {|
  datamem_start := MemoryLayout.heap_start ml;
  datamem_pastend := MemoryLayout.heap_pastend ml;
  goodTrace t := exists s0 s, good_trace s0 t s;
  isReady t m := exists s0 s, good_trace s0 t s /\ exists bs R, memrep bs R s m |}.

Lemma good_trace_from_isRead a a0 : isReady garagedoor_spec a a0 ->
  isReady garagedoor_spec a a0 /\
  ExprImpEventLoopSpec.goodTrace garagedoor_spec a.
Proof.
  cbv [isReady goodTrace garagedoor_spec]; intuition eauto.
  case H as (?&?&?&?&?&H); eauto.
Qed.

Lemma link_initfn : spec_of_initfn funcs.
Proof.
  eapply initfn_ok.
  eapply memconst_ok.
  eapply lan9250_init_ok;
    try (eapply lan9250_wait_for_boot_ok || eapply lan9250_mac_write_ok);
    (eapply lan9250_readword_ok || eapply lan9250_writeword_ok);
        eapply spi_xchg_ok;
        (eapply spi_write_ok || eapply spi_read_ok).
Qed. Optimize Heap.

Import ToplevelLoop GoFlatToRiscv .
Local Notation invariant := (ll_inv compile_ext_call ml garagedoor_spec).
Lemma invariant_proof :
  forall initial : MetricRiscvMachine,
    getPc (getMachine initial) = MemoryLayout.code_start ml ->
    getNextPc (getMachine initial) = word.add (getPc (getMachine initial)) (word.of_Z 4)->
    regs_initialized.regs_initialized (getRegs (getMachine initial)) ->
    getLog (getMachine initial) = [] ->
    (forall a, word.unsigned (MemoryLayout.code_start ml) <= word.unsigned a < word.unsigned (MemoryLayout.code_pastend ml) -> In a (getXAddrs (getMachine initial))) ->
    valid_machine initial ->
    (imem (MemoryLayout.code_start ml) (MemoryLayout.code_pastend ml) garagedoor_insns *
     LowerPipeline.mem_available (MemoryLayout.heap_start ml) (MemoryLayout.heap_pastend ml) *
     LowerPipeline.mem_available (MemoryLayout.stack_start ml) (MemoryLayout.stack_pastend ml))%sep (getMem (getMachine initial)) ->

     invariant initial /\
     (forall st, invariant st -> mcomp_sat (run1 Decode.RV32IM) st invariant /\
       exists extend s0 s1, good_trace s0 (extend ++ getLog (getMachine st)) s1).
Proof.
  intros.

  unshelve epose proof compiler_invariant_proofs _ _ _ _ _ garagedoor_spec as HCI; shelve_unifiable; try exact _.
  { exact (naive_word_riscv_ok 5%nat). }
  { eapply SortedListString.ok. }
  { eapply compile_ext_call_correct. }
  { intros. cbv [compile_ext_call compile_interact]; BreakMatch.break_match; trivial. }
  { exact ml_ok. }
  ssplit; intros; ssplit; eapply HCI; eauto; [].

  econstructor.
  eexists garagedoor_insns.
  eexists garagedoor_finfo.
  eexists garagedoor_stack_size.
  rewrite garagedoor_compiler_result_ok; ssplit; trivial using compiler_emitted_valid_instructions.
  2,3:vm_compute; inversion 1.
  econstructor (* ProgramSatisfiesSpec *).
  1: vm_compute; reflexivity.
  1: instantiate (1:=snd init).
  3: instantiate (1:=snd loop).
  1,3: exact eq_refl.
  1,2: cbv [hl_inv]; intros; eapply WeakestPreconditionProperties.sound_cmd.
  1,3: eapply Crypto.Util.Bool.Reflect.reflect_bool; vm_compute; reflexivity.

  all : repeat straightline; subst args.
  { repeat straightline.
    cbv [LowerPipeline.mem_available LowerPipeline.ptsto_bytes] in *.
    cbv [datamem_pastend datamem_start garagedoor_spec heap_start heap_pastend ml] in H6.
    SeparationLogic.extract_ex1_and_emp_in H6.
    change (BinIntDef.Z.of_nat (Datatypes.length anybytes) = 0x2000) in H6_emp0.
    Tactics.rapply WeakestPreconditionProperties.Proper_call;
      [|eapply link_initfn]; try eassumption.
    2: {
      rewrite <-(List.firstn_skipn 0x40 anybytes) in H6.
      rewrite <-(List.firstn_skipn 0x20 (List.skipn _ anybytes)) in H6.
      do 2 seprewrite_in @Array.bytearray_append H6.
      rewrite 2firstn_length, skipn_length, 2Nat2Z.inj_min, Nat2Z.inj_sub, H6_emp0 in H6.
      split.
      { use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 0%nat; [|ecancel_done].
        Morphisms.f_equiv. }
      { rewrite firstn_length, skipn_length. Lia.lia. }
      { Lia.lia. } }
    intros ? ? ? ?; repeat straightline; eapply good_trace_from_isRead.
    subst a; rewrite app_nil_r.
    rewrite <-(List.firstn_skipn 0x20 (List.firstn _ anybytes)) in H11.
    rewrite <-(List.firstn_skipn 1520 (skipn 32 (skipn 64 anybytes))) in H11.
    do 2 seprewrite_in @Array.bytearray_append H11.
    rewrite ?firstn_length, ?skipn_length, ?Nat2Z.inj_min, ?Nat2Z.inj_sub, H6_emp0 in H11.
    cbv [isReady garagedoor_spec good_trace]. eexists (_,_), (_,_); fwd. eauto.
    { rewrite <-app_nil_l. eapply TracePredicate.concat_app; eauto. econstructor. }
    cbv [memrep]. ssplit.
    { use_sep_assumption. cancel.
      cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
      cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
      cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
      ecancel_done. }
    all : repeat rewrite ?firstn_length, ?skipn_length; try Lia.lia. }

  {  match goal with H : goodTrace _ _ |- _ => clear H end.
    cbv [isReady goodTrace good_trace garagedoor_spec] in *; repeat straightline.
    DestructHead.destruct_head' state.
    Tactics.rapply WeakestPreconditionProperties.Proper_call;
      [|eapply link_loopfn]; try eassumption.
    intros ? ? ? ?; repeat straightline; eapply good_trace_from_isRead.
    eexists; fwd; try eassumption.
    cbv [good_trace] in *; repeat straightline.
    { subst a.  (eexists; split; [eapply Forall2_app; eauto|]).
      eapply stateful_app_r, stateful_singleton; eauto. } }

  Unshelve.
  all : trivial using SortedListString.ok.
Qed.

(*
Print Assumptions link_loopfn. (* Closed under the global context *)
Print Assumptions invariant_proof. (* propositional_extensionality, functional_extensionality_dep *)
*)
