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
  require ($(1536 - 1) < ethertype);
  protocol = (load1(buf+$23))&$0xff;
  r = (protocol == $0x11)
))).

Definition memcpy : func := ("memcpy", (["dst"; "src"; "n"], [], bedrock_func_body:(
  while len {
    store1(dst, load1(src));

    dst = dst + $1;
    src = src + $1;
    len = len - $1
  }
))).

Definition memswap : func := ("memswap", (["x"; "y"; "len"], [], bedrock_func_body:(
  while len {
    vx = load1(x);
    vy = load1(y);
    store1(x, vy);
    store1(y, vx);

    x = x + $1;
    y = y + $1;
    len = len - $1
  }
))).

Definition memequal : func := ("memequal", (["x"; "y"; "len"], ["r"], bedrock_func_body:(
  r = $0;
  while len {
    r = r | (load1(x) ^ load1(y));

    x = x + $1;
    y = y + $1;
    len = len - $1
  };
  r = r == $0
))).

Definition loop : func := ("loop", (["buf"; "seed"; "theirpk"], [], bedrock_func_body:(
  unpack! l, err = recvEthernet(buf);
  require !err;
  require $(42+32) == l;
  unpack! t = is_udp(buf);
  require t;

  stackalloc 64 as st;
  chacha20_block(seed, (*nonce*)st, st);
  memcpy(seed, st, $16);
  x25519_base(buf+$42, st+$16); (* TODO: from_bytes / to_bytes *)
  memswap(buf, buf+$6, $6);
  memswap(buf+$(18+12), buf+$(18+16), $4);
  memswap(buf+$(18+20), buf+$(18+22), $2);
  lan9250_tx(buf, $(42+32));

  x25519(st, st+$16, theirpk);
  unpack! l, err = recvEthernet(buf);
  require !err;
  require $(42+16) == l;
  unpack! t = is_udp(buf);
  require t;
  unpack! set0 = memequal(st, buf+$42, $16);
  unpack! set1 = memequal(st+$16, buf+$42, $16);

  io! mmio_val = MMIOREAD($0x1001200c);
  mmio_val = mmio_val & coq:(Z.clearbit (Z.clearbit (2^32-1) 23) 22); (* TODO: pin numbering, init *)
  output! MMIOWRITE($0x1001200c, mmio_val | (set1<<$1 | set0) << $22)
))).

Definition funcs : list func :=
  [ loop; is_udp; memcpy; memswap; memequal; x25519; x25519_base;

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
    fe25519_scmula24 ].

(*
Require Import bedrock2.ToCString.
Compute c_module funcs.
*)

Derive montladder_compiler_result SuchThat
       (compile
         (compile_ext_call (funname_env:=SortedListString.map))
         (map.of_list funcs) = Success montladder_compiler_result)
       As montladder_compiler_result_ok.
Proof.
  (*
error:("The register allocator replaced source variable" "len" "by target variable" 22 "but when the checker encountered this pair," "its current mapping of source to target variables" 
[("x1101", 21); ("src", 9); ("x0101", 20); ("dst", 8); 
("x1001", 19); ("x0001", 18)] "did not contain the pair" 
("len", 22)) = Success ?Goal
   *)

  vm_compute. apply f_equal. subst; exact eq_refl.
Qed.
