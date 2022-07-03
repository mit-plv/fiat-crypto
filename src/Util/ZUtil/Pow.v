Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma base_pow_neg b n : n < 0 -> b^n = 0.
  Proof.
    destruct n; intro H; try reflexivity; compute in H; congruence.
  Qed.

  Lemma nonneg_pow_pos a b : 0 < a -> 0 < a^b -> 0 <= b.
  Proof.
    destruct (Z_lt_le_dec b 0); intros; auto.
    erewrite Z.pow_neg_r in * by eassumption.
    lia.
  Qed.
  Global Hint Resolve nonneg_pow_pos (fun n => nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
  Lemma nonneg_pow_pos_helper a b dummy : 0 < a -> 0 <= dummy < a^b -> 0 <= b.
  Proof. eauto with zarith lia. Qed.
  Global Hint Resolve nonneg_pow_pos_helper (fun n dummy => nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.

  Lemma div_pow2succ : forall n x, (0 <= x) ->
    n / 2 ^ Z.succ x = Z.div2 (n / 2 ^ x).
  Proof.
    intros.
    rewrite Z.pow_succ_r, Z.mul_comm by auto.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
    rewrite Zdiv2_div.
    reflexivity.
  Qed.

  Definition pow_sub_r'
    := fun a b c y H0 H1 => @Logic.eq_trans _ _ _ y (@Z.pow_sub_r a b c H0 H1).
  Definition pow_sub_r'_sym
    := fun a b c y p H0 H1 => Logic.eq_sym (@Logic.eq_trans _ y _ _ (Logic.eq_sym p) (@Z.pow_sub_r a b c H0 H1)).

  Lemma two_p_two_eq_four : 2^(2) = 4.
  Proof. reflexivity. Qed.
End Z.
Hint Rewrite Z.base_pow_neg using zutil_arith : zsimplify.
Hint Rewrite <- Z.two_p_two_eq_four : push_Zpow.
Global Hint Resolve Z.pow_sub_r' Z.pow_sub_r'_sym Z.eq_le_incl : zarith.
Global Hint Resolve (fun b => f_equal (fun e => b ^ e)) (fun e => f_equal (fun b => b ^ e)) : zarith.
Global Hint Resolve Z.nonneg_pow_pos (fun n => Z.nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
Global Hint Resolve Z.nonneg_pow_pos_helper (fun n dummy => Z.nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.
