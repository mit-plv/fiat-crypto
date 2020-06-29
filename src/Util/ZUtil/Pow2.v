Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Module Z.
  Lemma pow2_ge_0: forall a, (0 <= 2 ^ a)%Z.
  Proof.
    intros; apply Z.pow_nonneg; lia.
  Qed.

  Lemma pow2_gt_0: forall a, (0 <= a)%Z -> (0 < 2 ^ a)%Z.
  Proof.
    intros; apply Z.pow_pos_nonneg; [|assumption]; lia.
  Qed.

  Lemma pow2_lt_or_divides : forall a b, 0 <= b ->
    2 ^ a < 2 ^ b \/ (2 ^ a) mod 2 ^ b = 0.
  Proof.
    intros a b H.
    destruct (Z_lt_dec a b); [left|right].
    { apply Z.pow_lt_mono_r; auto; lia. }
    { replace a with (a - b + b) by ring.
      rewrite Z.pow_add_r by lia.
      apply Z.mod_mul, Z.pow_nonzero; lia. }
  Qed.
End Z.
