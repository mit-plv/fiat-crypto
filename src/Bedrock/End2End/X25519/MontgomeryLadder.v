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
Require Import bedrock2.BasicC32Semantics bedrock2.Syntax bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.OfListWord Coq.Init.Byte coqutil.Byte.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
Definition x25519_gallina := montladder_gallina (Field.M_pos(FieldParameters:=field_parameters)) Field.a24 (Z.to_nat (Z.log2 (Z.pos order))).
Global Instance spec_of_x25519 : spec_of x25519 :=
  fnspec! "x25519" out sk pk / (o s p : list Byte.byte) (R : mem -> Prop),
  { requires t m := m =* s$@sk * p$@pk * o$@out * R /\
      length s = 32%nat /\ length p = 32%nat /\ length o = 32%nat /\ byte.unsigned (nth 31 p x00) <= 0x7f;
    ensures t' m := t=t' /\ m=* s$@sk ⋆ p$@pk ⋆ R ⋆
      (le_split 32 (x25519_gallina (le_combine s) (Field.feval_bytes p)))$@out }.

Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.
Local Instance spec_of_fe25519_from_bytes : spec_of "fe25519_from_bytes" := Field.spec_of_from_bytes.
Local Instance spec_of_fe25519_to_bytes : spec_of "fe25519_to_bytes" := Field.spec_of_to_bytes.
Local Instance spec_of_montladder : spec_of "montladder" := spec_of_montladder(Z.to_nat (Z.log2 Curve25519.order)).
Lemma x25519_ok : program_logic_goal_for_function! x25519.
Proof.
  repeat straightline.
  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H2. { transitivity 40%nat; trivial. }

  straightline_call; ssplit.
  { eexists. ecancel_assumption. }
  { unfold Field.FElem.
    use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 0%nat; cbn; trivial. eapply RelationClasses.reflexivity. }
  { unfold Field.bytes_in_bounds, frep25519, field_representation, Signature.field_representation, Representation.frep.
    match goal with |- ?P ?x ?z => let y := eval cbv in x in change (P y z) end; cbn.
    repeat (destruct p as [|? p]; try (cbn in *;discriminate); []).
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

  unfold FElem in H22. extract_ex1_and_emp_in H22.
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
  fnspec! "x25519_base" out sk / (o s : list Byte.byte) (R : mem -> Prop),
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

Require Import bedrock2Examples.LAN9250.
Require Import bedrock2Examples.lightbulb.
Require Import bedrock2Examples.chacha20.
Require Import bedrock2Examples.memequal.
Require Import bedrock2Examples.memswap.
Require Import bedrock2Examples.memconst.
Require Import Rupicola.Examples.Net.IPChecksum.IPChecksum.

Import Syntax.Coercions.

Definition is_udp : func := ("is_udp", (["buf"], ["r"], bedrock_func_body:(
  ethertype = (((load1(buf + $12))&$0xff) << $8) | ((load1(buf + $13))&$0xff);
  require ($(1536 - 1) < ethertype) else { r = $0 };
  protocol = (load1(buf+$23))&$0xff;
  r = (protocol == $0x11)
))).

Import Coq.Init.Byte.
Definition garageowner : list byte :=
  [x7b; x06; x18; x0c; x54; x0c; xca; x9f; xa3; x16; x0b; x2f; x2b; x69; x89; x63; x77; x4c; xc1; xef; xdc; x04; x91; x46; x76; x8b; xb2; xbf; x43; x0e; x34; x34].

Definition st : expr := 0x8000000.
Definition pk : expr := 0x8000040.
Definition buf : expr := 0x8000060.

Definition init : func :=
  ("init", ([], [], bedrock_func_body:(
    $(memconst "pk" garageowner)($pk);
    output! MMIOWRITE($0x10012038, $(Z.lor (Z.shiftl (0xf) 2) (Z.shiftl 1 9)));
    output! MMIOWRITE($0x10012008, $(Z.lor (Z.shiftl 1 11) (Z.shiftl 1 12)));
    output! MMIOWRITE($0x10024010, $2);
    unpack! err = lan9250_init()
  ))).

Definition loop : func := ("loop", ([], [], bedrock_func_body:(
  st=$st; pk=$pk; buf=$buf;
  unpack! l, err = recvEthernet(buf);
  require !err;
  if $(14+20+8 +32 +2+4) == l { (* getpk *)
    unpack! t = is_udp(buf);
    require t;

    memswap(buf, buf+$6, $6); (* ethernet address *)
    memswap(buf+$(14+12), buf+$(14+16), $4); (* IP address *)
    memswap(buf+$(14+20+0), buf+$(14+20+2), $2); (* UDP port *)
    store1(buf+$(14+2), $0); (* ip length *)
    store1(buf+$(14+3), $(20+ 8+ 32+2)); (* ip length *)
    store1(buf+$(14+10), $0); (* preliminary ip checksum *)
    store1(buf+$(14+11), $0); (* preliminary ip checksum *)

    unpack! chk = ip_checksum(buf+$14, $20);
    store1(buf+$(14+11), chk>>$8);
    store1(buf+$(14+10), chk);

    store1(buf+$(14+20+4), $0); (* udp length *)
    store1(buf+$(14+20+5), $(8+ 32+2)); (* udp length *)
    store1(buf+$(14+20+6), $0); (* udp checksum *)
    store1(buf+$(14+20+7), $0); (* udp checksum *)

    x25519_base(buf+$42, st+$32);
    lan9250_tx(buf, $(14+20+8+32+2))
  } else if $(14+20+8 +16 +2+4) == l { (* operate *)
    unpack! t = is_udp(buf);
    require t;

    stackalloc 32 as tmp;
    x25519(tmp, st+$32, pk);
    unpack! set0 = memequal(tmp, buf+$(14+20+8), $16);
    unpack! set1 = memequal(tmp+$16, buf+$(14+20+8), $16);

    io! mmio_val = MMIOREAD($0x1001200c);
    mmio_val = mmio_val & coq:(Z.clearbit (Z.clearbit (2^32-1) 11) 12);
    output! MMIOWRITE($0x1001200c, mmio_val | (set1<<$1 | set0) << $11);

    if (set0|set1) { (* rekey *)
        chacha20_block(st, st, (*nonce*)pk, $0) (* NOTE: another impl? *)
    }
  }
))).

Definition funcs : list func :=
  [ init;
    loop; is_udp; memswap; memequal; x25519; x25519_base; lan9250_tx;
    memconst "pk" garageowner;

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
    fe25519_scmula24 ]
    ++ lightbulb.function_impls
    ++ [chacha20_quarter; chacha20_block]
    ++ [ip_checksum_br2fn].


Definition montladder_c_module := ToCString.c_module funcs.

Require compiler.ToplevelLoop.
Definition ml: MemoryLayout.MemoryLayout(word:=BasicC32Semantics.word) := {|
  MemoryLayout.code_start    := word.of_Z 0x20400000;
  MemoryLayout.code_pastend  := word.of_Z 0x21400000;
  MemoryLayout.heap_start    := word.of_Z 0x80000000;
  MemoryLayout.heap_pastend  := word.of_Z 0x80002000;
  MemoryLayout.stack_start   := word.of_Z 0x80002000;
  MemoryLayout.stack_pastend := word.of_Z 0x80004000;
|}.



Derive garagedoor_compiler_result SuchThat
  (ToplevelLoop.compile_prog (string_keyed_map:=@SortedListString.map) MMIO.compile_ext_call ml (map.of_list funcs)
  = Success garagedoor_compiler_result)
  As garagedoor_compiler_result_ok.
Proof.
  match goal with x := _ |- _ => cbv delta [x]; clear x end.
  vm_compute.
  match goal with |- @Success ?A ?x = Success ?e => is_evar e;
    exact (@eq_refl (result A) (@Success A x)) end.
Qed.

Set Printing Implicit.
Definition garagedoor_stack_size := snd garagedoor_compiler_result.
Definition garagedoor_finfo := snd (fst garagedoor_compiler_result).
Definition garagedoor_insns := fst (fst garagedoor_compiler_result).
Definition garagedoor_bytes := Pipeline.instrencode garagedoor_insns.
Definition garagedoor_symbols : list byte := Symbols.symbols garagedoor_finfo.

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         (map.of_list funcs) = Success montladder_compiler_result)
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
