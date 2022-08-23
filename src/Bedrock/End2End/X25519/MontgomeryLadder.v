Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
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
            (Z.to_nat (Z.log2_up Curve25519.l))
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

Definition memcpy : func := ("memcpy", (["dst"; "src"; "n"], [], bedrock_func_body:(
  while n {
    store1(dst, load1(src));

    dst = dst + $1;
    src = src + $1;
    n = n - $1
  }
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

Definition init : func :=
  ("init", ([], [], bedrock_func_body:(
    output! MMIOWRITE($0x10012038, $(Z.lor (Z.shiftl (0xf) 2) (Z.shiftl 1 9)));
    output! MMIOWRITE($0x10012008, $(Z.lor (Z.shiftl 1 11) (Z.shiftl 1 12)));
    output! MMIOWRITE($0x10024010, $2);
    unpack! err = lan9250_init()
  ))).


Definition loop : func := ("loop", (["buf"; "st"(*seed+k0+k1*); "theirpk"], [], bedrock_func_body:(
  unpack! l, err = recvEthernet(buf);
  require !err;
  if $(14+20+8 +32 +2+4) == l {
    unpack! t = is_udp(buf);
    require t;
    chacha20_block(st, st, (*nonce*)theirpk, $0); (* NOTE: another impl? *)
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
    x25519(st+$32, st+$32, theirpk)
  } else if $(14+20+8 +16 +2+4) == l {
    unpack! t = is_udp(buf);
    require t;
    unpack! set0 = memequal(st+$32, buf+$(14+20+8), $16);
    unpack! set1 = memequal(st+$(32+16), buf+$(14+20+8), $16);

    io! mmio_val = MMIOREAD($0x1001200c);
    mmio_val = mmio_val & coq:(Z.clearbit (Z.clearbit (2^32-1) 11) 12);
    output! MMIOWRITE($0x1001200c, mmio_val | (set1<<$1 | set0) << $11);

    if (set0|set1) {
        chacha20_block(st, st, (*nonce*)theirpk, $0) (* NOTE: another impl? *)
    }
  }
))).

Require Import bedrock2Examples.LAN9250.
Require Import bedrock2Examples.lightbulb.
Require Import bedrock2Examples.chacha20.

Definition funcs : list func :=
  [ init;
    loop; is_udp; memcpy; memswap; memequal; x25519; x25519_base; lan9250_tx;

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

Require Import bedrock2.ToCString.
Compute ToCString.c_module funcs.

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         (map.of_list funcs) = Success montladder_compiler_result)
       As montladder_compiler_result_ok.
Proof.
  vm_compute. apply f_equal. subst; exact eq_refl.
Qed.
