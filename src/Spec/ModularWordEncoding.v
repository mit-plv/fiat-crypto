Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Bedrock.Word.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.WordUtil.
Require Import Crypto.Spec.Encoding.
Require Crypto.Encoding.ModularWordEncodingPre.

Local Open Scope nat_scope.

Section ModularWordEncoding.
  Context {m : positive} {sz : nat} {m_pos : (0 < m)%Z} {bound_check : Z.to_nat m < 2 ^ sz}.

  Definition Fm_enc (x : F m) : word sz := NToWord sz (Z.to_N (F.to_Z x)).

  Definition Fm_dec (x_ : word sz) : option (F m) :=
    let z := Z.of_N (wordToN (x_)) in
    if Z_lt_dec z m
      then Some (F.of_Z m z)
      else None
  .

  Definition sign_bit (x : F m) :=
  match (Fm_enc x) with
    | Word.WO => false
    | Word.WS b _ w' => b
  end.

  Global Instance modular_word_encoding : canonical encoding of F m as word sz := {
    enc := Fm_enc;
    dec := Fm_dec;
    encoding_valid :=
      @ModularWordEncodingPre.Fm_encoding_valid m sz m_pos bound_check;
    encoding_canonical :=
      @ModularWordEncodingPre.Fm_encoding_canonical m sz bound_check
  }.

End ModularWordEncoding.