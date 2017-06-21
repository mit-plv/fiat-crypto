Require Import Coq.ZArith.ZArith Coq.QArith.QArith QArith.Qround.

Local Open Scope Z_scope.

Lemma pow_ceil_mul_nat_nonzero b f
      (b_nz:b <> 0)
      (f_pos:(0 <= f)%Q)
  : forall i, b^Qceiling (f * inject_Z (Z.of_nat i)) <> 0.
Proof.
  intros.
  eapply Z.pow_nonzero; try omega.
  rewrite Zle_Qle.
  eapply Qle_trans; [|eapply Qle_ceiling].
  eapply Qle_trans; [|eapply (Qmult_le_compat_r 0)]; trivial.
  cbv; discriminate.
  apply (Qle_trans _ (inject_Z 0)); [eapply Qle_refl|].
  rewrite <-Zle_Qle.
  eapply Zle_0_nat.
Qed.