(*** Compute the modular inverse of a ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.Nat2Z.
Require Import Crypto.Util.ZUtil.Z2Nat.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Wf1.
Local Open Scope Z_scope.

Module Z.
  Import Znumtheory.
  Definition invmod a m := fst (fst (extgcd a m)) mod m.
  Notation modinv := invmod (only parsing).

  Lemma invmod_0_l m : invmod 0 m = 0. Proof. reflexivity. Qed.

  Lemma invmod_ok a m (Hm : m <> 0) : invmod a m * a mod m = Z.gcd a m mod m.
  Proof.
    cbv [invmod]; destruct extgcd as [[u v]g] eqn:H.
    eapply extgcd_correct in H; case H as [[]]; subst; cbn [fst snd].
    rewrite Z.mul_mod_idemp_l by trivial.
    erewrite <-Z.mod_add, H; trivial.
  Qed.

  Lemma invmod_coprime' a m (Hm : m <> 0) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1 mod m.
  Proof. rewrite invmod_ok, H; trivial. Qed.

  Lemma invmod_coprime a m (Hm : 2 <= m) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1.
  Proof. rewrite invmod_coprime', Z.mod_1_l; trivial. Admitted.

  Lemma invmod_prime a m (Hm : prime m) (H : a mod m <> 0) : invmod a m * a mod m = 1.
  Proof.
    pose proof prime_ge_2 _ Hm as Hm'.
    rewrite Z.mod_divide in H (* by lia *) by (intro; subst m; auto using not_prime_0).
    apply invmod_coprime, Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; auto.
  Qed.

  Lemma modinv_correct a m
        (Hm : 0 < m)
        (Hgcd : Z.gcd (Z.abs a) m = 1)
    : (a * modinv a m) mod m = 1 mod m /\ 0 <= modinv a m < m.
  Proof.
    rewrite Z.gcd_abs_l in Hgcd.
    rewrite Z.mul_comm, invmod_coprime';
    cbv [invmod]; repeat split; try (Z.div_mod_to_equations; lia).
  Qed.
End Z.
