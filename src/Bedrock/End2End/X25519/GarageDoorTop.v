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
Import Crypto.Bedrock.End2End.RupicolaCrypto.ChaCha20.
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
  &[, (* Main loop *) init; loop; initfn; loopfn;

    (* Ethernet & SPI drivers *)
    lan9250_tx; recvEthernet; lan9250_init;
    lan9250_wait_for_boot; lan9250_mac_write;
    lan9250_writeword; lan9250_readword;
    SPI.spi_xchg; SPI.spi_write; SPI.spi_read;

    (* "Standard library" of bedrock2 *)
    memswap; memequal; memconst_pk;

    (* Generated using Rupicola *)
    ip_checksum; chacha20_block; quarter]

    (* X25519, generated code and handwritten wrappers *)
  ++MontgomeryLadder.funcs.

(*
Compute (length funcs-3)%nat. (* functions excluding main-loop boilerplate *)
Compute ((length MontgomeryLadder.funcs - 2 + 3))%nat. (* generated functions *)
Compute (length funcs-3 - (length MontgomeryLadder.funcs - 2 + 3))%nat. (* handwritten functions *)
Compute bedrock2.ToCString.c_module funcs.
*)

Lemma chacha20_ok: forall functions,
    map.get functions "chacha20_block" = Some ChaCha20.chacha20_block ->
    map.get functions "quarter" = Some ChaCha20.quarter ->
    ChaCha20.spec_of_chacha20 functions.
Proof.
  intros.
  simple eapply ChaCha20.chacha20_block_body_correct; [constructor | eassumption | ].
  eapply ChaCha20.quarter_body_correct; [constructor | eassumption ].
Qed.

Ltac pose_correctness lem :=
  let H := fresh in
  pose proof (lem (map.of_list funcs)) as H;
  unfold program_logic_goal_for in H;
  repeat lazymatch type of H with
    | map.get (map.of_list _) _ = Some _ -> _ => specialize (H eq_refl)
    end.

Import SPI.
Lemma link_loopfn : spec_of_loopfn (map.of_list funcs).
Proof.
  pose_correctness loopfn_ok.
  pose_correctness memswap.memswap_ok.
  pose_correctness memequal_ok.
  pose_correctness recvEthernet_ok.
  pose_correctness lan9250_readword_ok.
  pose_correctness spi_xchg_ok.
  pose_correctness spi_write_ok.
  pose_correctness spi_read_ok.
  pose_correctness (ip_checksum_br2fn_ok I).
  pose_correctness x25519_base_ok.
  pose_correctness fe25519_from_word_correct.
  pose_correctness fe25519_to_bytes_correct.
  pose_correctness lan9250_tx_ok.
  pose_correctness lan9250_writeword_ok.
  pose_correctness x25519_ok.
  pose_correctness fe25519_from_bytes_correct.
  pose_correctness chacha20_ok.
  assert (spec_of_montladder (map.of_list funcs)). {
    unfold spec_of_montladder, ScalarMult.MontgomeryLadder.spec_of_montladder.
    intros.
    eapply WP.extend_env_wp_call.
    2: { eapply link_montladder. eassumption. }
    clear. unfold funcs.
    (* TODO this could be more computational *)
    intros k v G.
    unfold MontgomeryLadder.funcs, map.of_list in G.
    rewrite ?map.get_put_dec in G.
    repeat (destruct_one_match_hyp; [inversion G; subst; reflexivity | ]).
    rewrite map.get_empty in G. discriminate G.
  }
  repeat match goal with
         | HI: ?A -> _, HA: ?A |- _ => specialize (HI HA)
         end.
  assumption.
Qed.

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
(*
Compute length garagedoor_bytes.
*)
Definition garagedoor_symbols : list byte := Symbols.symbols garagedoor_finfo.

Require Import compiler.CompilerInvariant.
Require Import compiler.NaiveRiscvWordProperties.
Local Existing Instance SortedListString.map.
Import TracePredicate TracePredicateNotations SPI lightbulb_spec.
Import GarageDoor.

Lemma compiler_emitted_valid_instructions :
  bverify.bvalidInstructions Decode.RV32IM garagedoor_insns = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Definition good_trace(s : state)(t : Semantics.trace)(s' : state) :=
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

Lemma link_initfn : spec_of_initfn (map.of_list funcs).
Proof.
  pose_correctness initfn_ok.
  pose_correctness lan9250_init_ok.
  pose_correctness lan9250_wait_for_boot_ok.
  pose_correctness lan9250_mac_write_ok.
  pose_correctness lan9250_readword_ok.
  pose_correctness lan9250_writeword_ok.
  pose_correctness spi_xchg_ok.
  pose_correctness spi_write_ok.
  pose_correctness spi_read_ok.
  unfold spec_of_memconst_pk in *.
  pose_correctness (memconst_ok "memconst_pk" garageowner).
  repeat match goal with
         | HI: ?A -> _, HA: ?A |- _ => specialize (HI HA)
         end.
  assumption.
Qed. Optimize Heap.

Import ToplevelLoop GoFlatToRiscv regs_initialized LowerPipeline.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Import bedrock2.Map.Separation. Local Open Scope sep_scope.
Require Import bedrock2.ReversedListNotations.
Local Notation run_one_riscv_instr := (mcomp_sat (run1 Decode.RV32IM)).
Local Notation RiscvMachine := MetricRiscvMachine.
Implicit Types mach : RiscvMachine.

Theorem garagedoor_invariant_proof: exists invariant: RiscvMachine -> Prop,
   (forall mach,
    getPc mach = code_start ml /\
    getNextPc mach = getPc mach ^+ /[4] /\
    regs_initialized (getRegs mach) /\
    getLog mach = [] /\
    (forall a, \[code_start ml] <= \[a] < \[code_pastend ml] -> In a (getXAddrs mach)) /\
    valid_machine mach /\
    (imem (code_start ml) (code_pastend ml) garagedoor_insns ⋆
     mem_available (heap_start ml) (heap_pastend ml) ⋆
     mem_available (stack_start ml) (stack_pastend ml)) (getMem mach)
    -> invariant mach) /\
   (forall mach, invariant mach -> run_one_riscv_instr mach invariant) /\
   (forall mach, invariant mach -> exists extend s0 s1, good_trace s0 (getLog mach ;++ extend) s1).
Proof.
  exists (ll_inv compile_ext_call ml garagedoor_spec).
  unshelve epose proof compiler_invariant_proofs _ _ _ _ _ garagedoor_spec as HCI; shelve_unifiable; try exact _.
  { exact (naive_word_riscv_ok 5%nat). }
  { eapply SortedListString.ok. }
  { eapply compile_ext_call_correct. }
  { intros. cbv [compile_ext_call compile_interact]; BreakMatch.break_match; trivial. }
  { exact ml_ok. }
  ssplit; intros; ssplit; eapply HCI; eauto; [].

  clear HCI. destruct H as (? & ? & ? & ? & ? & ? & ?).
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
  1,2: cbv [hl_inv]; intros; eapply MetricSemantics.of_metrics_free; eapply WeakestPreconditionProperties.sound_cmd.

  all : repeat straightline; subst args.
  { cbv [LowerPipeline.mem_available LowerPipeline.ptsto_bytes] in *.
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
    intros ? m ? ?; repeat straightline; eapply good_trace_from_isRead.
    subst a; rewrite app_nil_r.
    lazymatch goal with H: sep _ _ m |- _ => rename H into M end.
    rewrite <-(List.firstn_skipn 0x20 (List.firstn _ anybytes)) in M.
    rewrite <-(List.firstn_skipn 1520 (skipn 32 (skipn 64 anybytes))) in M.
    do 2 seprewrite_in @Array.bytearray_append M.
    rewrite ?firstn_length, ?skipn_length, ?Nat2Z.inj_min, ?Nat2Z.inj_sub, H6_emp0 in M.
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
Print Assumptions garagedoor_invariant_proof. (* propositional_extensionality, functional_extensionality_dep *)
*)
