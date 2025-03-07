From Coq Require Import ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.LetIn.
Local Open Scope Z_scope.

Module Z.
    Lemma signed_small s v (Hv : (0 <= v <= Z.ones (Z.of_N s-1))) : Z.signed s v = v.
    Proof.
        destruct (N.eq_dec s 0); subst; cbv [Z.signed].
        { rewrite Z.land_0_r. cbn in *; Lia.lia. }
        rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
        rewrite Z.ones_equiv in Hv.
        rewrite Z.mod_small; try ring.
        enough (2 ^ Z.of_N s = 2 ^ (Z.of_N s - 1) + 2 ^ (Z.of_N s - 1))%Z; try Lia.lia.
        replace (Z.of_N s) with (1+(Z.of_N s-1))%Z at 1 by Lia.lia.
        rewrite Z.pow_add_r; try Lia.lia.
    Qed.

    Lemma signed_0 s : Z.signed s 0 = 0.
    Proof.
        destruct (N.eq_dec s 0); subst; trivial.
        cbv [Z.signed].
        rewrite !Z.land_ones, !Z.shiftl_mul_pow2, ?Z.add_0_r, ?Z.mul_1_l by Lia.lia.
        rewrite Z.mod_small; try ring.
        split; try (eapply Z.pow_lt_mono_r; Lia.lia).
        eapply Z.pow_nonneg; Lia.lia.
    Qed.
    #[global]
    Hint Rewrite signed_0 : zsimplify_const zsimplify zsimplify_fast.
    Global Hint Resolve signed_0 : zarith.
End Z.