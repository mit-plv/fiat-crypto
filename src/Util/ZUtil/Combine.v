Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope Z_scope.

Module Z.
  Lemma combine_at_bitwidth_correct bitwidth lo hi
  : Z.combine_at_bitwidth bitwidth lo hi = lo + (hi << bitwidth).
  Proof. reflexivity. Qed.

  Lemma combine_at_bitwidth_Proper bitwidth
    : Proper (Z.le ==> Z.le ==> Z.le) (Z.combine_at_bitwidth bitwidth).
  Proof.
    cbv [Proper respectful]; intros; rewrite !combine_at_bitwidth_correct.
    destruct bitwidth as [|bitwidth|bitwidth];
      [ | assert (0 <= 2^Z.pos bitwidth) by (apply Z.pow_nonneg; lia).. ];
      rewrite ?Z.shiftl_mul_pow2, ?Z.shiftl_div_pow2, ?Z.pow_0_r by lia; cbn [Z.opp]; try nia;
        Z.div_mod_to_quot_rem; nia.
  Qed.
  Hint Resolve combine_at_bitwidth_Proper : zarith.

  Lemma combine_at_bitwidth_Proper1 bitwidth x
    : Proper (Z.le ==> Z.le) (Z.combine_at_bitwidth bitwidth x).
  Proof. repeat intro; eapply combine_at_bitwidth_Proper; (eassumption + reflexivity). Qed.
  Hint Resolve combine_at_bitwidth_Proper1 : zarith.

  Lemma combine_at_bitwidth_Proper2 bitwidth x
    : Proper (Z.le ==> Z.le) (fun y => Z.combine_at_bitwidth bitwidth y x).
  Proof. repeat intro; eapply combine_at_bitwidth_Proper; (eassumption + reflexivity). Qed.
  Hint Resolve combine_at_bitwidth_Proper2 : zarith.
End Z.
