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
Require Import bedrock2Examples.chacha20.
Require Import bedrock2Examples.memequal.
Require Import bedrock2Examples.memswap.
Require Import bedrock2Examples.memconst.
Require Import Rupicola.Examples.Net.IPChecksum.IPChecksum.

Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry.
Import ListNotations.
Import Coq.Init.Byte.

Definition garageowner : list byte :=
  [x7b; x06; x18; x0c; x54; x0c; xca; x9f; xa3; x16; x0b; x2f; x2b; x69; x89; x63; x77; x4c; xc1; xef; xdc; x04; x91; x46; x76; x8b; xb2; xbf; x43; x0e; x34; x34].

Local Notation ST := 0x80000000.
Local Notation PK := 0x80000040.
Local Notation BUF:= 0x80000060.

Definition initfn : func :=
  ("initfn", ([], [], bedrock_func_body:(
    $(memconst "pk" garageowner)($PK);
    output! MMIOWRITE($0x10012038, $(Z.lor (Z.shiftl (0xf) 2) (Z.shiftl 1 9)));
    output! MMIOWRITE($0x10012008, $(Z.lor (Z.shiftl 1 11) (Z.shiftl 1 12)));
    output! MMIOWRITE($0x10024010, $2);
    unpack! err = lan9250_init()
  ))).

Definition loopfn : func := ("loopfn", ([], [], bedrock_func_body:(
  st=$ST; pk=$PK; buf=$BUF;
  unpack! l, err = recvEthernet(buf);
  require !err;
  require ($63 < l);

  ethertype = (((load1(buf + $12))&$0xff) << $8) | ((load1(buf + $13))&$0xff);
  require ($(1536 - 1) < ethertype);
  protocol = (load1(buf+$23))&$0xff;
  require (protocol == $0x11);

  if $(14+20+8 +2+32 +4) == l { (* getpk *)
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

    x25519_base(buf+$(14+20+8 +2), st+$32);
    unpack! err = lan9250_tx(buf, $(14+20+8 +2+32))
  } else if $(14+20+8 +2+16 +4) == l { (* operate *)
    stackalloc 32 as tmp;
    x25519(tmp, st+$32, pk);
    unpack! set0 = memequal(tmp, buf+$(14+20+8 +2), $16);
    unpack! set1 = memequal(tmp+$16, buf+$(14+20+8 +2), $16);

    io! mmio_val = MMIOREAD($0x1001200c);
    mmio_val = mmio_val & coq:(Z.clearbit (Z.clearbit (2^32-1) 11) 12);
    output! MMIOWRITE($0x1001200c, mmio_val | (set1<<$1 | set0) << $11);

    if (set0|set1) { (* rekey *)
        chacha20_block(st, st, (*nonce*)pk, $0) (* NOTE: another impl? *)
    }
  }
))).

Import TracePredicate TracePredicateNotations SPI lightbulb_spec.
Notation OP := (lightbulb_spec.OP _).
Definition iocfg : list OP -> Prop :=
  one ("st", word.of_Z (0x10012038), word.of_Z (Z.lor (Z.shiftl (0xf) 2) (Z.shiftl 1 9))) +++
  one ("st", word.of_Z (0x10012008), word.of_Z (Z.lor (Z.shiftl 1 11) (Z.shiftl 1 12))) +++
  one ("st", word.of_Z (0x10024010), word.of_Z 2).
Definition BootSeq : list OP -> Prop :=
  iocfg +++ (lan9250_init_trace _
               ||| lan9250_boot_timeout _
               ||| (any+++spi_timeout _)).

Import WeakestPrecondition ProgramLogic SeparationLogic.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
Global Instance spec_of_initfn : spec_of initfn :=
  fnspec! "initfn" / bs R,
  { requires t m := m =* bs $@(word.of_Z PK) * R /\ length bs = 32%nat;
    ensures t' m' := m' =* garageowner$@(word.of_Z PK) * R /\
      exists iol, t' = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\
      BootSeq ioh }.

Ltac fwd :=
  repeat match goal with
         | |- _ /\ _ => split
         | |- exists _, _ => eexists
         | _ => straightline
         end; trivial.
Ltac slv := try solve [ trivial | ecancel_assumption | SepAutoArray.listZnWords | intuition idtac | reflexivity | eassumption].

Local Instance spec_of_memconst_pk : spec_of "memconst_pk" := spec_of_memconst "pk" garageowner.
Local Instance WHY_spec_of_lan9250_init : spec_of lan9250_init := spec_of_lan9250_init.
Lemma initfn_ok : program_logic_goal_for_function! initfn.
Proof.
  repeat straightline.
  straightline_call.
  { ssplit. eassumption. rewrite H2. all : vm_compute; trivial. }
  repeat straightline.
  eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
  eexists; fwd; slv.
  { vm_compute. intuition congruence. }
  eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
  eexists; fwd; slv.
  { vm_compute. intuition congruence. }
  eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
  eexists; fwd; slv.
  { vm_compute. intuition congruence. }
  straightline_call; repeat straightline; fwd.
  { repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app). }
  { repeat (eapply List.Forall2_cons || eapply List.Forall2_refl || eapply List.Forall2_app; eauto). all: cbv[mmio_event_abstraction_relation]; eauto. }
  cbv [BootSeq ].
  eapply TracePredicate.concat_app.
  2: solve[cbv [choice]; intuition eauto].
  cbv [iocfg].
  eapply (TracePredicate.concat_app _ _ [_;_] [_]); [|cbv [one]; trivial].
  eapply (TracePredicate.concat_app _ _ [_] [_]); cbv [one]; trivial.
Qed.

Local Open Scope list_scope.
Require Crypto.Bedrock.End2End.RupicolaCrypto.Spec.
Import Tuple LittleEndianList.
Local Definition be2 z := rev (le_split 2 z).
Local Coercion to_list : tuple >-> list.
Local Coercion Z.b2z : bool >-> Z.

Definition state : Type := list byte * list byte. (* seed, xs25519 secret key *)

Definition garagedoor_iteration : state -> list (lightbulb_spec.OP _) -> state -> Prop :=
  fun '(seed, sk) ioh '(SEED, SK) =>
  (lightbulb_spec.lan9250_recv_no_packet _ ioh \/
    lightbulb_spec.lan9250_recv_packet_too_long _ ioh \/
    TracePredicate.concat TracePredicate.any (lightbulb_spec.spi_timeout _) ioh) \/
  (exists incoming, lightbulb_spec.lan9250_recv _ incoming ioh /\
  let ethertype := le_combine (rev (firstn 2 (skipn 12 incoming))) in ethertype < 1536 \/
  let ipproto := nth 23 incoming x00 in ipproto <> x11 \/
  (length incoming <> 14+20+8 +2+16 +4 /\ length incoming <> 14+20+8 +2+32 +4)%nat) \/
  exists (mac_local mac_remote : tuple byte 6),
  exists (ethertype : Z) (ih_const : tuple byte 2) (ip_length : Z) (ip_idff : tuple byte 5),
  exists (ipproto := x11) (ip_checksum : Z) (ip_local ip_remote : tuple byte 4),
  exists (udp_local udp_remote : tuple byte 2) (udp_length : Z) (udp_checksum : Z),
  exists (garagedoor_header : tuple byte 2) (garagedoor_payload : list byte),
  let incoming : list byte :=
    (mac_local ++ mac_remote ++ be2 ethertype ++
     ih_const ++ be2 ip_length ++
     ip_idff ++ [ipproto] ++ le_split 2 ip_checksum ++
     ip_remote ++ ip_local ++
     udp_remote ++ udp_local ++
     be2 udp_length ++ be2 udp_checksum ++
     garagedoor_header ++ garagedoor_payload) in
  (exists doorstate action : Naive.word32,
  TracePredicate.concat
      (lightbulb_spec.lan9250_recv _ incoming) (TracePredicate.concat
      (TracePredicate.one ("ld", lightbulb_spec.GPIO_DATA_ADDR _, doorstate))
      (TracePredicate.one ("st", lightbulb_spec.GPIO_DATA_ADDR _, action))) ioh
   /\ (
    let m := firstn 16 garagedoor_payload in
    let v := le_split 32 (F.to_Z (x25519_gallina (le_combine sk) (Field.feval_bytes(FieldRepresentation:=frep25519) garageowner))) in
    exists set0 set1 : Naive.word32,
    (word.unsigned set0 = 1 <-> firstn 16 v = m) /\
    (word.unsigned set1 = 1 <->  skipn 16 v = m) /\
    action = word.or (word.and doorstate (word.of_Z (Z.clearbit (Z.clearbit (2^32-1) 11) 12))) (word.slu (word.or (word.slu set1 (word.of_Z 1)) set0) (word.of_Z 11)) /\
    (* /\ (word.unsigned set0 <> 0 \/ word.unsigned set1 <> 0 -> SEED++SK = RupicolaCrypto.Spec.chacha20_encrypt k (Z.to_nat (word.unsigned counter)) _ _) *)
    (word.unsigned set1 = 0 -> word.unsigned set0 = 0 -> SEED=seed /\ SK=sk))) \/
  TracePredicate.concat (lightbulb_spec.lan9250_recv _ incoming)
  (lightbulb_spec.lan9250_send _
    (let ip_length := 62 in
     let udp_length := 42 in
     mac_remote ++ mac_local ++ be2 ethertype ++
     let ih C := ih_const ++ be2 ip_length ++
                 ip_idff ++ [ipproto] ++ le_split 2 C ++
                 ip_local ++ ip_remote in
     ih (Spec.ip_checksum (ih 0)) ++
     udp_local ++ udp_remote ++
     be2 udp_length ++ be2 0 ++
     garagedoor_header ++
     le_split 32 (F.to_Z (x25519_gallina (le_combine sk) (F.of_Z Field.M_pos 9)))))
  ioh /\ SEED=seed /\ SK=sk.

Local Instance spec_of_recvEthernet : spec_of "recvEthernet" := spec_of_recvEthernet.
Local Instance spec_of_lan9250_tx : spec_of "lan9250_tx" := spec_of_lan9250_tx.
Local Instance spec_of_memswap : spec_of "memswap" := spec_of_memswap.
Local Instance spec_of_memequal : spec_of "memequal" := spec_of_memequal.

Local Instance spec_of_chacha20 : spec_of "chacha20_block" :=
  fnspec! "chacha20_block" out key nonce counter / (pt k n : list Byte.byte) (R Rk Rn : map.rep -> Prop),
  { requires t m :=
      m =* pt$@out * R /\ length pt = 64%nat /\
      m =* k$@key * Rk /\ length k = 32%nat /\
      m =* n$@nonce * Rn /\ length n = 12%nat;
    ensures T m := T = t /\ exists ct, m =* ct$@out * R /\ length ct = 64%nat /\
      ct = RupicolaCrypto.Spec.chacha20_encrypt k (Z.to_nat (word.unsigned counter)) n pt }.

Definition memrep bs R : state -> map.rep(map:=SortedListWord.map _ _) -> Prop := fun '(seed, sk) m =>
  m =*
    seed$@(word.of_Z ST) *
    sk$@(word.add (word.of_Z ST) (word.of_Z 32)) *
    garageowner$@(word.of_Z PK) *
    bs $@(word.of_Z BUF) * R /\
  length seed = 32%nat /\
  length sk = 32%nat /\
  length bs = 1520%nat.

Global Instance spec_of_loopfn : spec_of loopfn :=
  fnspec! "loopfn" / seed sk bs R,
  { requires t m := memrep bs R (seed, sk) m;
    ensures T M := exists SEED SK BS, memrep BS R (SEED, SK) M /\
    exists iol, T = iol ++ t /\
    exists ioh, SPI.mmio_trace_abstraction_relation ioh iol /\
    garagedoor_iteration (seed, sk) ioh (SEED, SK) }.

Import ZnWords.
Import coqutil.Tactics.autoforward.

Import Crypto.Util.FixCoqMistakes.

Lemma loopfn_ok : program_logic_goal_for_function! loopfn.
Proof.
  straightline.
  cbv [memrep garagedoor_iteration] in *.
  repeat straightline.
  rename H11 into Lseed. rename H12 into Lsk. rename H13 into H11.
  straightline_call; try ecancel_assumption; trivial; repeat straightline.
  intuition idtac; repeat straightline;
  eexists; split; repeat straightline; split; intros; try contradiction; [|]; repeat straightline.
  2: fwd; slv.

  pose proof H12 as Hbuf.
  seprewrite_in @bytearray_index_merge Hbuf. { ZnWords. }

  eexists; split; repeat straightline.
  rewrite word.unsigned_ltu, ?word.unsigned_of_Z_nowrap by ZnWords.ZnWords;
  destr Z.ltb; rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; intuition try discriminate;
  autoforward with typeclass_instances in E.
  2: { fwd; slv. right. left. fwd; slv; intuition try ZnWords. }

  repeat straightline.
  eapply WeakestPreconditionProperties.dexpr_expr.
  eexists; split; repeat straightline.

  case (SepAutoArray.list_expose_nth x3 12 ltac:(ZnWords)) as (Hpp&Lpp).
  forget (List.firstn 12 x3) as mac.
  forget (nth 12 x3 Inhabited.default) as ethertype_hi.
  forget (List.skipn 13 x3) as pp.
  subst x3.
  repeat seprewrite_in @Array.bytearray_append H12; cbn [Array.array] in H12.
  rewrite ?app_length in *; cbn [length] in *; rewrite ?Lpp in *.
  change (Z.of_nat 12) with 12 in *.

  repeat straightline.

  destruct pp as [|ethertype_lo pp]; cbn [length app Array.array] in *.
  { exfalso; ZnWords. }
  Import SetEvars coqutil.Tactics.eplace Word.Naive LittleEndianList.
  eplace (word.add (word.add buf _) _) with (word.add buf _) in H12 by (ring_simplify; trivial).
  repeat straightline.

  let v := constr:(word.or (word.slu (word.and v0 v1) v2) (word.and v4 v5)) in
  remember v as ethertype in *;
  assert (word.unsigned ethertype = le_combine [ethertype_lo; ethertype_hi]);
   [ rewrite Heqethertype | ]; clear Heqethertype.
  { pose proof byte.unsigned_range ethertype_hi.
    pose proof byte.unsigned_range ethertype_lo.
    subst v0 v1 v2 v3 v4 v5.
    cbn [le_combine]; rewrite ?Z.shiftl_0_l, ?Z.lor_0_r.
    rewrite_strat (bottomup (terms word.unsigned_or_nowrap word.unsigned_and_nowrap word.unsigned_of_Z word.unsigned_slu)).
    2: ZnWords.
    change (word.wrap 255) with (Z.ones 8) in *; rewrite !Z.land_ones by Lia.lia.
    cbv [word.wrap]; (rewrite_strat (bottomup (terms (Zmod_small)))); try ZnWords.ZnWords.
    { rewrite Z.lor_comm; reflexivity. } }

  eexists; split; repeat straightline.
  rewrite word.unsigned_ltu, ?word.unsigned_of_Z_nowrap by ZnWords.ZnWords;
  destr Z.ltb; rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; intuition try discriminate;
  autoforward with typeclass_instances in E0.
  2: {
    fwd; slv; [].
    right. left. eexists. ssplit; try eassumption. left.
    rewrite skipn_app, skipn_all2, ?Lpp, ?app_nil_l by ZnWords.
    cbn [List.skipn minus firstn List.firstn List.app rev]. ZnWords. }

  case (SepAutoArray.list_expose_nth pp 9 ltac:(ZnWords)) as (Hppp&Lppp).
  forget (List.firstn 9 pp) as ih_l.
  forget (nth 9 pp Inhabited.default) as ipproto.
  forget (List.skipn 10 pp) as ppp.
  subst pp.
  repeat seprewrite_in @Array.bytearray_append H12; cbn [Array.array] in H12.
  rewrite ?app_length in *; cbn [length] in *; rewrite ?Lppp in *.
  change (Z.of_nat 9) with 9 in *.
  change (Z.of_nat 1) with 1 in *.

  repeat eplace (word.add (word.add buf _) _) with (word.add buf _) in H12 by (ring_simplify; trivial).

  repeat straightline.
  eexists; split; repeat straightline.
  subst protocol.
  pose proof byte.unsigned_range ipproto.
  rewrite word.unsigned_eqb, ?word.unsigned_and_nowrap, ?word.unsigned_of_Z_nowrap by ZnWords.ZnWords.
  change (255) with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by ZnWords.
  destr Z.eqb; rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; intuition try discriminate; autoforward with typeclass_instances in E1.
  2: {
    fwd; slv; [].
    right. left. eexists. ssplit; try eassumption. right. left.
    rewrite app_nth2 by ZnWords.
    rewrite app_comm_cons.
    rewrite app_nth2 by SepAutoArray.listZnWords.
    rewrite app_nth2 by SepAutoArray.listZnWords.
    rewrite app_nth1 by SepAutoArray.listZnWords.
    match goal with |- context[nth ?x] => replace x with O by SepAutoArray.listZnWords end.
    cbn. intro. subst. apply E1. reflexivity. }

  repeat straightline.
  eexists; split; repeat straightline.
  rewrite word.unsigned_eqb, ?word.unsigned_of_Z_nowrap by ZnWords.ZnWords.
  destr Z.eqb; rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; intuition try discriminate; autoforward with typeclass_instances in E2.

  2: {
    repeat straightline.
    eexists; split; repeat straightline.
    rewrite word.unsigned_eqb, ?word.unsigned_of_Z_nowrap by ZnWords.ZnWords.
    destr Z.eqb; rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1; intuition try discriminate; autoforward with typeclass_instances in E3.
    2: {
      fwd; slv.
      right. left. eexists. ssplit; try eassumption. right. right. SepAutoArray.listZnWords. }
    repeat straightline.
    straightline_call; ssplit; try ecancel_assumption; try trivial; try ZnWords.
    { cbv. inversion 1. }

    rename Lppp into Lihl; assert (List.length ppp = 40)%nat as Lppp by ZnWords.

    repeat straightline.
    pose proof (List.firstn_skipn (14+20+8 +2 - 12-2-9-1) ppp) as HH.
    pose proof (@firstn_length_le _ ppp (14+20+8 +2 - 12-2-9-1) ltac:(ZnWords)).
    pose proof skipn_length (14+20+8 +2 - 12-2-9-1) ppp; rewrite Lppp in *.
    forget (List.firstn (14+20+8 +2 - 12-2-9-1) ppp) as pPP.
    forget (List.skipn (14+20+8 +2 - 12-2-9-1) ppp) as pPPP.
    simpl minus in H31, H32.
    subst ppp.
    repeat rewrite ?(app_assoc _ _ pPPP), ?app_comm_cons in H33.
    do 3 (seprewrite_in @Array.bytearray_append H33; cbn [Array.array] in H33).

    change (unsigned x) with (@word.unsigned _ word32 x) in H32.
    repeat straightline.
    pose proof (List.firstn_skipn 16 pPPP) as HH.
    pose proof (@firstn_length_le _ pPPP 16 ltac:(ZnWords)).
    pose proof skipn_length 16 pPPP. rewrite H32 in *.
    forget (List.firstn 16 pPPP) as cmp1.
    forget (List.skipn 16 pPPP) as trailer.
    subst pPPP.
    seprewrite_in_by (Array.bytearray_append cmp1) H33 SepAutoArray.listZnWords.

    remember (le_split 32 (F.to_Z (x25519_gallina (le_combine sk) (Field.feval_bytes _)))) as vv.
    repeat straightline.
    pose proof (List.firstn_skipn 16 vv) as Hvv.
    pose proof (@firstn_length_le _ vv 16 ltac:(subst vv; rewrite ?length_le_split; ZnWords)).
    pose proof skipn_length 16 vv.
    forget (List.firstn 16 vv) as vv0.
    forget (List.skipn 16 vv) as vv1.
    subst vv.
    rewrite <-Hvv in H33.
    rewrite length_le_split in *.
    seprewrite_in_by (Array.bytearray_append vv0) H33 SepAutoArray.listZnWords.

    repeat straightline.
    straightline_call; ssplit.
    { ecancel_assumption. }
    { use_sep_assumption. cancel. cancel_seps_at_indices 2%nat 0%nat.
      { Morphisms.f_equiv. SepAutoArray.listZnWords. }
      ecancel_done. }
    { ZnWords. }
    { ZnWords. }
    repeat straightline.

    repeat straightline.
    straightline_call; ssplit.
    { use_sep_assumption. cancel. cancel_seps_at_indices 1%nat 0%nat.
      { Morphisms.f_equiv. SepAutoArray.listZnWords. }
      ecancel_done. }
    { use_sep_assumption. cancel. cancel_seps_at_indices 2%nat 0%nat.
      { Morphisms.f_equiv. SepAutoArray.listZnWords. }
      ecancel_done. }
    { ZnWords. }
    { ZnWords. }

    repeat straightline.
    eexists. split. repeat straightline.
    eexists _, _; split; [eapply map.split_empty_r; reflexivity|].
    eexists; ssplit; trivial.
    { cbv. clear. intuition congruence. }

    repeat straightline.
    eexists. split. repeat straightline.
    eexists _, _; split; [eapply map.split_empty_r; reflexivity|].
    eexists; ssplit; trivial.
    eexists; ssplit; trivial.
    { cbv. clear. intuition congruence. }
    repeat straightline.

    eapply map.split_empty_r in H38; destruct H38.
    eapply map.split_empty_r in H39; destruct H39.
    seprewrite_in_by @bytearray_index_merge H33 SepAutoArray.listZnWords.
    seprewrite_in_by @bytearray_index_merge H33 SepAutoArray.listZnWords.
    seprewrite_in_by @bytearray_index_merge H33 SepAutoArray.listZnWords.
    seprewrite_in_by @bytearray_index_merge H33 SepAutoArray.listZnWords.
    seprewrite_in_by @bytearray_index_merge H33 SepAutoArray.listZnWords.
    assert (length (vv0 ++ vv1) = 32%nat) by SepAutoArray.listZnWords.


    change (word.of_Z 134217728) with st in H33.
    repeat straightline.
    eexists; ssplit; repeat straightline.
    { (* chacha20 *)
      (* NOTE: viewing the same memory in two different ways, ++ combined and split *)
      straightline_call; ssplit.
      { seprewrite_in_by @bytearray_index_merge H33 SepAutoArray.listZnWords.
        ecancel_assumption. }
      { SepAutoArray.listZnWords. }
      { ecancel_assumption. }
      { SepAutoArray.listZnWords. }
      { rewrite <-(List.firstn_skipn 12 garageowner) in H33.
        seprewrite_in_by (Array.bytearray_append (List.firstn 12 garageowner)) H33 SepAutoArray.listZnWords.
        ecancel_assumption. }
      { SepAutoArray.listZnWords. }
      repeat straightline.

      rewrite <-(List.firstn_skipn 32 x6) in H46.
      seprewrite_in_by (Array.bytearray_append (List.firstn 32 x6)) H46 SepAutoArray.listZnWords.
      replace (word.of_Z (BinInt.Z.of_nat (Datatypes.length (List.firstn 32 x6)))) with (word.of_Z 32 : word32) in * by SepAutoArray.listZnWords.

      ssplit; trivial.
      eexists _, _, _; ssplit; try ecancel_assumption; try SepAutoArray.listZnWords.

    eexists; ssplit.
    { subst a0 a. change (?x::?y::?t) with ([x;y]++t). rewrite app_assoc. trivial. }
    eexists; ssplit.
    { eapply Forall2_app; try eassumption.
      eapply Forall2_cons. 2:eapply Forall2_cons. 3:eapply Forall2_nil.
      all:[>left|right]; eexists _, _; ssplit; trivial. }
    right.
    right.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. left; ssplit; trivial.
    eexists _, _.
    split.
    {
    eapply TracePredicate.concat_app.
    1: match goal with |- _ ?x _ => eplace x with _ end; [|eassumption].

    symmetry. (* NOTE: systematic list cancellation *)
    rewrite <-(firstn_skipn 6 mac) at 1; rewrite <-?app_assoc.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    change ([?x]++?y::?z) with ([x;y]++z).
    eapply (f_equal2 app).
    { cbv [be2]. progress change 2%nat with (List.length [ethertype_lo; ethertype_hi]).
      setoid_rewrite split_le_combine; trivial. }
    rewrite <-(firstn_skipn 2 ih_l) at 1; rewrite <-?app_assoc.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app).
    { cbv [be2]. eplace 2%nat with _ at 3; cycle 1.
      rewrite split_le_combine, rev_involutive; trivial.
      rewrite rev_length. SepAutoArray.listZnWords. }
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    eapply (f_equal2 app). { f_equal. eapply byte.unsigned_inj. rewrite E1. trivial. }
    rewrite <-(firstn_skipn 2 pPP) at 1; rewrite <-?app_assoc.
    eapply (f_equal2 app).
    { eplace 2%nat with _ at 2; cycle 1.
      rewrite split_le_combine; trivial.
      SepAutoArray.listZnWords. }
    rewrite <-(firstn_skipn 4 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 4 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app).
    { cbv [be2]. eplace 2%nat with _ at 7; cycle 1.
      rewrite split_le_combine, rev_involutive; trivial.
      rewrite rev_length. SepAutoArray.listZnWords. }
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app).
    { cbv [be2]. eplace 2%nat with _ at 8; cycle 1.
      rewrite split_le_combine, rev_involutive; trivial.
      rewrite rev_length. SepAutoArray.listZnWords. }
    eapply (f_equal2 app). { rewrite to_list_from_list; trivial. }
    reflexivity.

    change [?x;?y] with ([x]++[y]).
    eapply TracePredicate.concat_app; cbv [TracePredicate.one]; f_equal. }

    rewrite <-Hvv.
    rewrite !ListUtil.firstn_app_sharp by ZnWords.
    rewrite !ListUtil.skipn_app_sharp by ZnWords.
    eexists _, _; ssplit; try eassumption; subst mmio_val; eauto.

    intros; exfalso. apply H39.
    rewrite word.unsigned_or_nowrap. apply Z.lor_eq_0_iff; auto.
    (* end chacha20*) }

Optimize Proof. Optimize Heap.

    ssplit; trivial.
    eexists _, _, _; ssplit; try ecancel_assumption; try SepAutoArray.listZnWords.
    eexists; ssplit.
    { subst a. change (?x::?y::?t) with ([x;y]++t). rewrite app_assoc. trivial. }
    eexists; ssplit.
    { eapply Forall2_app; try eassumption.
      eapply Forall2_cons. 2:eapply Forall2_cons. 3:eapply Forall2_nil.
      all:[>left|right]; eexists _, _; ssplit; trivial. }
    right.
    right.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. left; ssplit; trivial.
    eexists _, _.
    split.
    {
    eapply TracePredicate.concat_app.
    1: match goal with |- _ ?x _ => eplace x with _ end; [|eassumption].

    symmetry. (* NOTE: systematic list cancellation *)
    rewrite <-(firstn_skipn 6 mac) at 1; rewrite <-?app_assoc.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    change ([?x]++?y::?z) with ([x;y]++z).
    eapply (f_equal2 app).
    { cbv [be2]. progress change 2%nat with (List.length [ethertype_lo; ethertype_hi]).
      setoid_rewrite split_le_combine; trivial. }
    rewrite <-(firstn_skipn 2 ih_l) at 1; rewrite <-?app_assoc.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app).
    { cbv [be2]. eplace 2%nat with _ at 3; cycle 1.
      rewrite split_le_combine, rev_involutive; trivial.
      rewrite rev_length. SepAutoArray.listZnWords. }
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    eapply (f_equal2 app). { f_equal. eapply byte.unsigned_inj. rewrite E1. trivial. }
    rewrite <-(firstn_skipn 2 pPP) at 1; rewrite <-?app_assoc.
    eapply (f_equal2 app).
    { eplace 2%nat with _ at 2; cycle 1.
      rewrite split_le_combine; trivial.
      SepAutoArray.listZnWords. }
    rewrite <-(firstn_skipn 4 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 4 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app); [rewrite to_list_from_list; trivial|].
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app).
    { cbv [be2]. eplace 2%nat with _ at 7; cycle 1.
      rewrite split_le_combine, rev_involutive; trivial.
      rewrite rev_length. SepAutoArray.listZnWords. }
    rewrite <-(firstn_skipn 2 (List.skipn _ _)) at 1; rewrite <-?app_assoc, ?List.skipn_skipn.
    eapply (f_equal2 app).
    { cbv [be2]. eplace 2%nat with _ at 8; cycle 1.
      rewrite split_le_combine, rev_involutive; trivial.
      rewrite rev_length. SepAutoArray.listZnWords. }
    eapply (f_equal2 app). { rewrite to_list_from_list; trivial. }
    reflexivity.

    change [?x;?y] with ([x]++[y]).
    eapply TracePredicate.concat_app; cbv [TracePredicate.one]; f_equal. }

    rewrite <-Hvv.
    rewrite !ListUtil.firstn_app_sharp by ZnWords.
    rewrite !ListUtil.skipn_app_sharp by ZnWords.
    eexists _, _; ssplit; try eassumption; subst mmio_val; eauto.
  }

  {
    repeat straightline.
    pose proof (List.firstn_skipn 6 mac) as HH.
    pose proof (@firstn_length_le _ mac 6 ltac:(ZnWords)).
    pose proof skipn_length 6 mac; rewrite ?Lpp in *.
    forget (List.firstn 6 mac) as mac_local.
    forget (List.skipn 6 mac) as mac_remote.
    subst mac.
    repeat seprewrite_in @Array.bytearray_append H12; cbn [Array.array] in H12.
    rewrite H26 in *.
    change (Z.of_nat 6) with 6 in *.

    straightline_call; ssplit; try ecancel_assumption; try ZnWords.

    repeat straightline.

    pose proof (List.firstn_skipn 2 ppp) as HH.
    pose proof (@firstn_length_le _ ppp 2 ltac:(ZnWords)).
    pose proof skipn_length 2 ppp as Lip_checksum.
    forget (List.firstn 2 ppp) as ip_checksum.
    forget (List.skipn 2 ppp) as pppp.
    subst ppp; rewrite ?app_length in *.
    repeat seprewrite_in @Array.bytearray_append H29; cbn [Array.array] in H29.
    rewrite ?H28 in *.
    change (Z.of_nat 24) with 24 in *.
    change (Z.of_nat 2) with 2 in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H29 by (ring_simplify; trivial).

    pose proof (List.firstn_skipn 4 pppp) as HH.
    pose proof (@firstn_length_le _ pppp 4 ltac:(ZnWords)).
    forget (List.firstn 4 pppp) as ip_remote.
    forget (List.skipn 4 pppp) as ppppp.
    subst pppp; rewrite ?app_length in *.
    repeat seprewrite_in @Array.bytearray_append H29; cbn [Array.array] in H29.
    rewrite ?H30 in *.
    change (Z.of_nat 28) with 28 in *.
    change (Z.of_nat 4) with 4 in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H29 by (ring_simplify; trivial).

    pose proof (List.firstn_skipn 4 ppppp) as HH.
    pose proof (@firstn_length_le _ ppppp 4 ltac:(ZnWords)).
    forget (List.firstn 4 ppppp) as ip_local.
    forget(List.skipn 4 ppppp) as pppppp.
    subst ppppp; rewrite ?app_length in *.
    repeat seprewrite_in @Array.bytearray_append H29; cbn [Array.array] in H29.
    rewrite ?H31 in *.
    change (Z.of_nat 30) with 30 in *.
    change (Z.of_nat 4) with 4 in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H29 by (ring_simplify; trivial).

    straightline_call; ssplit; try ecancel_assumption; try ZnWords.

    repeat straightline.

    pose proof (List.firstn_skipn 2 pppppp) as HH.
    pose proof (@firstn_length_le _ pppppp 2 ltac:(ZnWords)).
    forget (List.firstn 2 pppppp) as udp_remote.
    forget(List.skipn 2 pppppp) as pP.
    subst pppppp; rewrite ?app_length in *.
    repeat seprewrite_in @Array.bytearray_append H33; cbn [Array.array] in H33.
    rewrite ?H32 in *.
    change (Z.of_nat 34) with 34 in *.
    change (Z.of_nat 4) with 4 in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H33 by (ring_simplify; trivial).

    pose proof (List.firstn_skipn 2 pP) as HH.
    pose proof (@firstn_length_le _ pP 2 ltac:(ZnWords)).
    forget (List.firstn 2 pP) as udp_local.
    forget(List.skipn 2 pP) as pPP.
    subst pP; rewrite ?app_length in *.
    repeat seprewrite_in @Array.bytearray_append H33; cbn [Array.array] in H33.
    rewrite ?H34 in *.
    change (Z.of_nat 36) with 36 in *.
    change (Z.of_nat 4) with 4 in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H33 by (ring_simplify; trivial).

    straightline_call; ssplit; try ecancel_assumption; try ZnWords.

    repeat straightline.

    case (SepAutoArray.list_expose_nth ih_l 2 ltac:(ZnWords)) as (HH&LL).
    forget (List.firstn 2 ih_l) as ih_const.
    forget (nth 2 ih_l Inhabited.default) as ip_length_hi.
    forget (List.skipn 3 ih_l) as ip_length_lo.
    subst ih_l.
    repeat seprewrite_in @Array.bytearray_append H36; cbn [Array.array] in H36.
    rewrite ?app_length in *; cbn [length] in *; rewrite ?LL in *.
    change (Z.of_nat 1) with 1 in *.
    change (Z.of_nat 2) with 2 in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H36 by (ring_simplify; trivial).
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H36 by (ring_simplify; trivial).

    repeat straightline.

    destruct ip_length_lo as [|ip_length_lo ip_idff ].
    { cbn [length] in *. exfalso; Lia.lia. }
    cbn [Array.array] in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H35 by (ring_simplify; trivial).

    repeat straightline.
    destruct ip_checksum as [|ip_checksum_0 [|ip_checksum_1 [|] ] ];
        try (cbn [length] in *; discriminate); cbn [Array.array] in *.
    eplace (word.add (word.add buf _) _) with (word.add buf _) in H37 by (ring_simplify; trivial).

    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    repeat straightline.
    subst a7 a6 a5 a1 v9 v8 v7 v6.
    assert (ptsto_to_array :
      forall {width : Z} {word : Interface.word width},
      word.ok word ->
      forall mem : map.map (word.rep(word:=word)) Byte.byte,
      map.ok mem -> forall a b,
      Lift1Prop.iff1 (ptsto a b) (Array.array(mem:=mem) ptsto (word.of_Z 1) a [b])).
    { cbn [Array.array]. intros. cancel. }

    assert (bytearray_address_merge :
  forall {width : Z} {word : Interface.word width},
  word.ok word ->
  forall mem : map.map (word.rep(word:=word)) Byte.byte,
  map.ok mem ->
  forall (xs ys : list byte) (start b : word.rep),
  word.unsigned (word.sub b start) = Z.of_nat (Datatypes.length xs) ->
  Lift1Prop.iff1 (xs$@start ⋆ ys$@b) ((xs ++ ys)$@start : mem -> Prop)).
  { intros.
    replace b with (word.add start (word.sub b start)).
    { eapply Array.bytearray_index_merge; trivial. }
    eapply word.unsigned_inj. rewrite ?word.unsigned_add, ?word.unsigned_sub.
    cbv [word.wrap].
    rewrite Zplus_mod_idemp_r.
    transitivity (word.unsigned b mod 2^width).
    { f_equal.  ring. }
    rewrite Z.mod_small; trivial; eapply word.unsigned_range. }

Optimize Proof. Optimize Heap.

  repeat seprewrite_in @ptsto_to_array H39.
  rewrite ?word.unsigned_of_Z_nowrap in H39 by ZnWords.
  seprewrite_in_by (@bytearray_address_merge _ _ _ _ _ ih_const) H39 ZnWords.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.
  rewrite <-app_assoc in H39.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.
  rewrite <-!app_assoc in H39.
  cbn [length] in *.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.
  rewrite <-!app_assoc in H39.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.
  rewrite <-!app_assoc in H39.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.
  rewrite <-!app_assoc in H39.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.
  rewrite <-!app_assoc in H39.
  seprewrite_in_by (fun x=>@bytearray_address_merge _ _ _ _ _ (ih_const++x)%list) H39 SepAutoArray.listZnWords.

  straightline_call; [(ssplit; cycle -1)|];
    cbv [Arrays.listarray_value Arrays.ai_repr Arrays._access_info Arrays.ai_width Arrays.ai_size Arrays.ai_type Memory.bytes_per] in *;
    change (Z.of_nat 1) with 1%Z in *;
    try ecancel_assumption;
    try SepAutoArray.listZnWords.

Optimize Proof. Optimize Heap.

  repeat straightline.

  replace  ((ih_const ++ [byte.of_Z 0] ++ [byte.of_Z 62] ++ ip_idff ++ [ipproto] ++ [byte.of_Z 0] ++ [byte.of_Z 0] ++ ip_local) ++ ip_remote)%list
    with ((ih_const ++ [byte.of_Z 0] ++ [byte.of_Z 62] ++ ip_idff ++ [ipproto]) ++ [byte.of_Z 0] ++ [byte.of_Z 0] ++ ip_local ++ ip_remote)%list
    in * by (rewrite ?app_assoc; trivial).
  seprewrite_in @Array.bytearray_append H43.
  seprewrite_in (@Array.bytearray_append _ _ _ _ _ [byte.of_Z 0]) H43.
  seprewrite_in (@Array.bytearray_append _ _ _ _ _ [byte.of_Z 0]) H43.
  rewrite ?app_length in H43; cbn [length] in H43; rewrite ?LL in H43.
  replace (Datatypes.length ip_idff) with 5%nat in H43 by ZnWords.
  cbn [plus] in H43.
  repeat eplace (word.add (word.add buf _) _) with (word.add buf _) in H43 by (ring_simplify; trivial).

  Import symmetry.
  seprewrite_in (symmetry! (fun a=>@ptsto_to_array _ _ _ _ _ a (byte.of_Z 0))) H43.
  seprewrite_in (symmetry! (fun a=>@ptsto_to_array _ _ _ _ _ a (byte.of_Z 0))) H43.

  repeat straightline.
  revert H40.
  repeat match goal with H : sep _ _ _ |- _ => clear H end.
  repeat straightline.

  do 6 (destruct pPP as [|? pPP]; (cbn [Datatypes.length] in *; try Lia.lia)).
  set ((b :: b0 :: b1 :: b2 :: b3 :: b4 :: pPP)$@(word.add buf (word.of_Z 38))) as X in H40.
  cbn [Array.array] in X. subst X.
  repeat eplace (word.add (word.add buf _) _) with (word.add buf _) in H40 by (ring_simplify; trivial).

  repeat straightline.
  pose proof (List.firstn_skipn 32 pPP) as HH.
  pose proof (@firstn_length_le _ pPP 32 ltac:(ZnWords)).
  forget (List.firstn 32 pPP) as _pkpad.
  forget(List.skipn 32 pPP) as pPPP.
  subst pPP; rewrite ?app_length in *.
  repeat seprewrite_in (@Array.bytearray_append _ _ _ _ _ _pkpad) H29.
  rewrite ?H33 in *.
  change (Z.of_nat 32) with 32 in *.
  repeat eplace (word.add (word.add buf _) _) with (word.add buf _) in H29 by (ring_simplify; trivial).
  straightline_call; ssplit; try ecancel_assumption; trivial.

Optimize Proof. Optimize Heap.

  repeat straightline.

  revert H37.
  repeat match goal with H : sep _ _ _ |- _ => clear H end.
  intros.
  repeat seprewrite_in @ptsto_to_array H37.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 ZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
Optimize Proof. Optimize Heap.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
Optimize Proof. Optimize Heap.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
Optimize Proof. Optimize Heap.

  subst v6 v7 v8 v9 v10.
  rename x3 into ipchk.
  rewrite ?word.unsigned_sru_nowrap, ?word.unsigned_of_Z_nowrap in H37 by ZnWords.

  straightline_call; [ssplit; cycle -1|]; try ecancel_assumption.
  { rewrite ?app_length, ?length_le_split. SepAutoArray.listZnWords. }
  { ZnWords. }

  pose proof length_le_split 32 (F.to_Z (x25519_gallina (le_combine sk) (F.of_Z Field.M_pos 9))) as Hpkl.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.
  seprewrite_in_by (fun xs ys=>@bytearray_address_merge _ _ _ _ _ xs ys buf) H37 SepAutoArray.listZnWords.

  repeat straightline.
  destruct H35; repeat straightline; [intuition idtac | ].
  { eexists; ssplit. eexists _, _; ssplit; slv.
    eexists; ssplit. subst a4. subst a. rewrite app_assoc. reflexivity.
    eexists; ssplit. eapply Forall2_app; eassumption.
    eauto using TracePredicate.any_app_more. }

  ssplit; trivial.
  eexists _, _, _; ssplit; slv.
  eexists; ssplit. subst a4. subst a. rewrite app_assoc. reflexivity.
  eexists; ssplit. eapply Forall2_app; eassumption.
  right. right.

  exists (from_list 6 mac_local ltac:(assumption)); rewrite to_list_from_list.
  exists (from_list 6 mac_remote ltac:(assumption)); rewrite to_list_from_list.
  cbv beta delta [be2].
  exists (le_combine [ethertype_lo; ethertype_hi]); rewrite split_le_combine' by trivial.
  exists (from_list 2 ih_const ltac:(assumption)); rewrite to_list_from_list.
  exists (le_combine [ip_length_lo; ip_length_hi]); rewrite split_le_combine' by trivial.
  exists (from_list 5 ip_idff ltac:(ZnWords)); rewrite to_list_from_list.
  exists (le_combine [ip_checksum_0; ip_checksum_1]); rewrite split_le_combine' by trivial.
  exists (from_list 4 ip_local ltac:(assumption)); rewrite to_list_from_list.
  exists (from_list 4 ip_remote ltac:(assumption)); rewrite to_list_from_list.
  exists (from_list 2 udp_local ltac:(assumption)); rewrite to_list_from_list.
  exists (from_list 2 udp_remote ltac:(assumption)); rewrite to_list_from_list.
  exists (le_combine [b0; b]); rewrite split_le_combine' by trivial.
  exists (le_combine [b2; b1]); rewrite split_le_combine' by trivial.
  exists (from_list 2 [b3;b4] eq_refl); rewrite to_list_from_list.
  exists (_pkpad ++ pPPP).

  assert (x11 = ipproto) as Hp. { eapply byte.unsigned_inj. rewrite E1. trivial. }
  destruct Hp.

  right.
  ssplit; trivial.
  eapply TracePredicate.concat_app.
  all : match goal with |- _ ?x _ => eplace x with _; try eassumption; [] end.
  assert (app_singleton_l : forall {A} (x:A) xs, [x] ++ xs = x :: xs) by (intros; reflexivity).
  2 : simpl le_split at 1.
  all : cbn [rev].
  all : repeat (rewrite <-?app_assoc, ?app_nil_l, ?app_singleton_l, <-?app_comm_cons).
  all : trivial; repeat (f_equal; []).

  match goal with c := Impl.ip_checksum_impl ?y |- context[Spec.ip_checksum ?x] =>
    progress rewrite <-(Impl.ip_checksum_impl_ok' y : _ = word.unsigned c) in *;
    progress replace x with y in * end.
  2: {
    repeat (rewrite <-?app_assoc, ?app_nil_l, ?app_singleton_l, <-?app_comm_cons).
    trivial. }
  remember (Spec.ip_checksum _) as chk.
  unfold le_split at 1.
  repeat (rewrite <-?app_assoc, ?app_nil_l, ?app_singleton_l, <-?app_comm_cons).
  trivial. }

  Unshelve.
  all : try SepAutoArray.listZnWords.
Qed.

Require Import Crypto.Bedrock.End2End.X25519.MontgomeryLadderProperties.
Import bedrock2.Syntax.

(* these wrappers exist because CompilerInvariant requires execution proofs with arbitrary locals in the starting state, which ProgramLogic does not support *)
Definition init : func := ("init", ([], [], (cmd.call [] "initfn" []))).
Definition loop : func := ("loop", ([], [], (cmd.call [] "loopfn" []))).

Definition funcs : list Syntax.func :=
  [ init; loop;
    initfn; loopfn;
    memswap; memequal; memconst "pk" garageowner;
    ip_checksum_br2fn;
    chacha20_block; chacha20_quarter;
    lan9250_tx ]
    ++lightbulb.function_impls
    ++MontgomeryLadder.funcs.

Lemma chacha20_ok: forall functions, spec_of_chacha20 (chacha20_block::chacha20_quarter::functions).
Admitted.

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

Lemma compiler_emitted_valid_instructions :
  bverify.bvalidInstructions Decode.RV32IM garagedoor_insns = true.
Proof. vm_compute. reflexivity. Qed.

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
  1: instantiate (1:=snd (snd init)).
  3: instantiate (1:=snd (snd loop)).
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
Print Assumptions link_loopfn. (* chacha20_ok *)
Print Assumptions invariant_proof. (* chacha20_ok, propositional_extensionality, functional_extensionality_dep *)
*)
