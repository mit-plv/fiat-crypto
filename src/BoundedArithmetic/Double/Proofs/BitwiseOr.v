Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.

Section bitwise_or.
  Context {n W}
          {decode : decoder n W}
          {is_decode : is_decode decode}
          {or : bitwise_or W}
          {is_or : is_bitwise_or or}.

  Global Instance is_bitwise_or_double
    : is_bitwise_or or_double.
  Proof.
    constructor; intros x y.
    destruct n as [|p|].
    { rewrite !(tuple_decoder_n_O (W:=W) 2); easy. }
    { assert (0 <= Z.lor (decode (fst x)) (decode (fst y)) < 2^Z.pos p) by auto with zarith.
      rewrite (tuple_decoder_2 x), (tuple_decoder_2 y), (tuple_decoder_2 (or_double x y))
        by apply Zle_0_pos.
      push_decode.
      apply Z.bits_inj'; intros; autorewrite with Ztestbit.
      break_match; Z.ltb_to_lt; autorewrite with Ztestbit; reflexivity. }
    { rewrite !(tuple_decoder_n_neg (W:=W) 2); easy. }
  Qed.
End bitwise_or.
