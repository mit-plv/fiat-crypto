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
            (Z.to_nat (Z.log2 Curve25519.order))
            (field_parameters:=field_parameters)
            (field_representaton:=field_representation n s c))
       As montladder_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Import String.
Require Import bedrock2.NotationsCustomEntry.
Require Import Rupicola.Examples.Net.IPChecksum.IPChecksum.

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

Definition is_udp : func := ("is_udp", (["buf"], ["r"], bedrock_func_body:(
  ethertype = (((load1(buf + $12))&$0xff) << $8) | ((load1(buf + $13))&$0xff);
  require ($(1536 - 1) < ethertype) else { r = $0 };
  protocol = (load1(buf+$23))&$0xff;
  r = (protocol == $0x11)
))).

Definition memswap : func := ("memswap", (["x"; "y"; "n"], [], bedrock_func_body:(
  while n {
    vx = load1(x);
    vy = load1(y);
    store1(x, vy);
    store1(y, vx);

    x = x + $1;
    y = y + $1;
    n = n - $1
  }
))).

Definition memequal : func := ("memequal", (["x"; "y"; "n"], ["r"], bedrock_func_body:(
  r = $0;
  while n {
    r = r | (load1(x) ^ load1(y));

    x = x + $1;
    y = y + $1;
    n = n - $1
  };
  r = r == $0
))).

Import Syntax.Coercions.
Local Coercion Z.of_nat : nat >-> Z.

Definition from_const ident bs : func :=
  ("from_const_"++ident, (["p"], [], bedrock_func_body:(
    i = $0; while i < $(length bs) {
      store1(p, $(expr.inlinetable access_size.one bs "i"));
      p = p + $1;
      i = i + $1
    }
  ))).

Import Coq.Init.Byte.
Definition garageowner : list byte :=
  [x7b; x06; x18; x0c; x54; x0c; xca; x9f; xa3; x16; x0b; x2f; x2b; x69; x89; x63; x77; x4c; xc1; xef; xdc; x04; x91; x46; x76; x8b; xb2; xbf; x43; x0e; x34; x34].

Definition st : expr := 0x8000000.
Definition pk : expr := 0x8000040.
Definition buf : expr := 0x8000060.

Definition init : func :=
  ("init", ([], [], bedrock_func_body:(
    $(from_const "pk" garageowner)($pk);
    output! MMIOWRITE($0x10012038, $(Z.lor (Z.shiftl (0xf) 2) (Z.shiftl 1 9)));
    output! MMIOWRITE($0x10012008, $(Z.lor (Z.shiftl 1 11) (Z.shiftl 1 12)));
    output! MMIOWRITE($0x10024010, $2);
    unpack! err = lan9250_init()
  ))).

Definition loop : func := ("loop", ([], [], bedrock_func_body:(
  st=$st; pk=$pk; buf=$buf;
  unpack! l, err = recvEthernet(buf);
  require !err;
  if $(14+20+8 +32 +2+4) == l {
    unpack! t = is_udp(buf);
    require t;
    chacha20_block(st, st, (*nonce*)pk, $0); (* NOTE: another impl? *)
    x25519_base(buf+$42, st+$32);

    memswap(buf, buf+$6, $6); (* ethernet address *)
    memswap(buf+$(14+12), buf+$(14+16), $4); (* IP address *)
    memswap(buf+$(14+20+0), buf+$(14+20+2), $2); (* UDP port *)
    store1(buf+$(14+2), $0); (* ip length *)
    store1(buf+$(14+3), $(20+ 8+ 32+2)); (* ip length *)
    store1(buf+$(14+20+4), $0); (* udp length *)
    store1(buf+$(14+20+5), $(8+ 32+2)); (* udp length *)
    store1(buf+$(14+20+6), $0); (* udp checksum *)
    store1(buf+$(14+20+7), $0); (* udp checksum *)

    store1(buf+$(14+10), $0); (* preliminary ip checksum *)
    store1(buf+$(14+11), $0); (* preliminary ip checksum *)
    unpack! chk = ip_checksum(buf+$14, $20);
    store1(buf+$(14+11), chk>>$8);
    store1(buf+$(14+10), chk);

    lan9250_tx(buf, $(14+20+8+32+2));
    x25519(st+$32, st+$32, pk)
  } else if $(14+20+8 +16 +2+4) == l {
    unpack! t = is_udp(buf);
    require t;
    unpack! set0 = memequal(st+$32, buf+$(14+20+8), $16);
    unpack! set1 = memequal(st+$(32+16), buf+$(14+20+8), $16);

    io! mmio_val = MMIOREAD($0x1001200c);
    mmio_val = mmio_val & coq:(Z.clearbit (Z.clearbit (2^32-1) 11) 12);
    output! MMIOWRITE($0x1001200c, mmio_val | (set1<<$1 | set0) << $11);

    if (set0|set1) {
        chacha20_block(st, st, (*nonce*)pk, $0) (* NOTE: another impl? *)
    }
  }
))).

Require Import bedrock2Examples.LAN9250.
Require Import bedrock2Examples.lightbulb.
Require Import bedrock2Examples.chacha20.

Definition funcs : list func :=
  [ init;
    loop; is_udp; memswap; memequal; x25519; x25519_base; lan9250_tx;
    from_const "pk" garageowner;

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
