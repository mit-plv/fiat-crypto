Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.DivideExistsMul.
Require Import Crypto.Util.Tactics.DestructHead.
Local Open Scope Z_scope.

Module Z.
  Lemma divide_mul_div: forall a b c (a_nonzero : a <> 0) (c_nonzero : c <> 0),
    (a | b * (a / c)) -> (c | a) -> (c | b).
  Proof.
    intros ? ? ? ? ? divide_a divide_c_a; do 2 Z.divide_exists_mul.
    rewrite divide_c_a in divide_a.
    rewrite Z.div_mul' in divide_a by auto.
    replace (b * k) with (k * b) in divide_a by ring.
    replace (c * k * k0) with (k * (k0 * c)) in divide_a by ring.
    rewrite Z.mul_cancel_l in divide_a by (intuition auto with nia; rewrite H in divide_c_a; ring_simplify in divide_a; intuition).
    eapply Zdivide_intro; eauto.
  Qed.

  Lemma divide2_even_iff : forall n, (2 | n) <-> Z.even n = true.
  Proof.
    intros n; split. {
      intro divide2_n.
      Z.divide_exists_mul; [ | pose proof (Z.mod_pos_bound n 2); lia].
      rewrite divide2_n.
      apply Z.even_mul.
    } {
      intro n_even.
      pose proof (Zmod_even n) as H.
      rewrite n_even in H.
      apply Zmod_divide; lia || auto.
    }
  Qed.

  Lemma divide_pow_le b n m : 0 <= n <= m -> (b ^ n | b ^ m).
  Proof.
    intros. replace m with (n + (m - n)) by ring.
    rewrite Z.pow_add_r by lia.
    apply Z.divide_factor_l.
  Qed.

  Lemma mod_divide_full a b : (a mod b = 0) <-> (b | a).
  Proof.
    destruct (Z_zerop b); auto using Z.mod_divide; subst; [].
    rewrite Zmod_0_r; cbv [Z.divide]; intuition (destruct_head'_ex; subst; try exists 0; lia).
  Qed.

  Lemma mod_div_mod_full a m n : (n | m) -> a mod n = (a mod m) mod n.
  Proof.
    intros (p,Hp); rewrite (Z_div_mod_eq_full a m) at 1.
    rewrite Hp at 1.
    destruct (Z_zerop n); subst; try now autorewrite with zsimplify_const.
    rewrite Z.mul_shuffle0, Z.add_comm, Z.mod_add; auto.
  Qed.
  #[global]
   Hint Rewrite <- mod_div_mod_full using assumption : zsimplify push_Zmod.
End Z.
