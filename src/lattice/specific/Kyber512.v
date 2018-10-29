Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Require Import Crypto.lattice.Bytes.
Require Import Crypto.lattice.PolynomialRing.
Require Import Crypto.lattice.Spec.
Local Open Scope Z_scope.

Module Kyber512.
  Import Bytes.
  Definition n := 512%nat.
  Definition k := 2%nat.
  Definition q := 7681%positive.
  Definition log2q := Eval compute in (Pos.size q).
  Definition eta := 5%nat.
  Definition du := 11%positive.
  Definition dv := 3%positive.
  Definition dt := 11%positive.

  Definition pksize := Eval compute in (KyberSpec.pksize k n dt).
  Definition sksize := Eval compute in (KyberSpec.sksize k n log2q).
  Definition ciphertextsize := Eval compute in (KyberSpec.ciphertextsize k n du dv).
  Definition msgsize := Eval compute in (KyberSpec.msgsize n).

  (* TODO : fill in NTT stuff *)
  Axiom Rq_NTT : Type.
  Axiom Rq_NTTadd : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTmul : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTzero : Rq_NTT.
  Axiom NTT : @PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> @PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
  Axiom parse : stream -> Rq_NTT.
  Axiom XOF : stream -> stream.
  Axiom PRF : byte_array 32%nat * byte -> stream.
  Axiom G : stream -> byte_array 32%nat * byte_array 32%nat.
  Lemma nmod8 : (n mod 8 = 0)%nat. Proof. reflexivity. Qed.

  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen
         stream byte
         k eta n q log2q dt
         XOF PRF G
         (F q) (F.to_Z) (F.of_Z q)
         (@PolynomialRing.add n q)
         Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul
         NTT NTT_inv NTT_to_F
         nmod8
         nat_to_byte bytes_to_stream stream_to_bytes
         bytes_to_bits bits_to_bytes
         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc
         stream byte
         k eta n q dt du dv
         XOF PRF
         (F q) (F.to_Z) (F.of_Z q)
         (@PolynomialRing.add n q)
         Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul
         NTT NTT_inv
         nmod8
         byte0 nat_to_byte bytes_to_stream stream_to_bytes
         bytes_to_bits bits_to_bytes
         pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec
         byte
         k n q log2q du dv
         (F q) F.to_Z (F.of_Z q)
         (@PolynomialRing.sub n q)
         Rq_NTT Rq_NTTzero Rq_NTTadd Rq_NTTmul
         NTT NTT_inv NTT_of_F
         nmod8
         byte0
         bytes_to_bits bits_to_bytes
         sk c.
End Kyber512.
