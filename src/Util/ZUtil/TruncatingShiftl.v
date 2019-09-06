Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope Z_scope.

Module Z.
  Lemma truncating_shiftl_correct bw x y
  : Z.truncating_shiftl bw x y = (x << y) mod 2^bw.
  Proof. reflexivity. Qed.

  Lemma truncating_shiftl_correct_land_ones bw x y
  : Z.truncating_shiftl bw x y = (x << y) &' Z.ones (Z.max 0 bw).
  Proof.
    apply Z.max_case_strong; intro; rewrite truncating_shiftl_correct, ?Z.land_ones by lia;
      destruct (Z_zerop bw); subst; try reflexivity.
    rewrite Z.pow_neg_r, Z.pow_0_r, Zmod_0_r, Z.mod_1_r by lia; reflexivity.
  Qed.

  Lemma truncating_shiftl_correct_land_pow2 bw x y
  : Z.truncating_shiftl bw x y = (x << y) &' (2^(Z.max 0 bw) - 1).
  Proof.
    rewrite truncating_shiftl_correct_land_ones, Z.ones_equiv, <- Z.sub_1_r.
    reflexivity.
  Qed.
End Z.
