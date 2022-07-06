Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Lemma mul_split_at_bitwidth_mod bw x y : fst (Z.mul_split_at_bitwidth bw x y)  = (x * y) mod 2^bw.
  Proof.
    unfold Z.mul_split_at_bitwidth, LetIn.Let_In; break_innermost_match; Z.ltb_to_lt; try reflexivity;
      apply Z.land_ones; lia.
  Qed.
  Lemma mul_split_at_bitwidth_div bw x y : snd (Z.mul_split_at_bitwidth bw x y)  = (x * y) / 2^bw.
  Proof.
    unfold Z.mul_split_at_bitwidth, LetIn.Let_In; break_innermost_match; Z.ltb_to_lt; try reflexivity;
      apply Z.shiftr_div_pow2; lia.
  Qed.
  Lemma mul_split_mod s x y : fst (Z.mul_split s x y)  = (x * y) mod s.
  Proof.
    unfold Z.mul_split; break_match; Z.ltb_to_lt;
      [ rewrite mul_split_at_bitwidth_mod; congruence | reflexivity ].
  Qed.
  Hint Rewrite mul_split_mod : to_div_mod.
  Lemma mul_split_div s x y : snd (Z.mul_split s x y)  = (x * y) / s.
  Proof.
    unfold Z.mul_split; break_match; Z.ltb_to_lt;
      [ rewrite mul_split_at_bitwidth_div; congruence | reflexivity ].
  Qed.
  Hint Rewrite mul_split_div : to_div_mod.
End Z.

Module Export Hints.
  Export Crypto.Util.FixCoqMistakes.
  Export Crypto.Util.ZUtil.Definitions.Hints.
  Export Crypto.Util.ZUtil.Tactics.LtbToLt.Hints.
  Hint Rewrite Z.mul_split_mod : to_div_mod.
  Hint Rewrite Z.mul_split_div : to_div_mod.
End Hints.
