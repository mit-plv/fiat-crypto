Require Import Coq.ZArith.ZArith Coq.omega.Omega Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Sgn.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Local Open Scope Z_scope.

Module Z.
  Lemma quot_div_full a b : Z.quot a b = Z.sgn a * Z.sgn b * (Z.abs a / Z.abs b).
  Proof.
    destruct (Z_zerop b); [ subst | apply Z.quot_div; assumption ].
    destruct a; simpl; reflexivity.
  Qed.

  Local Arguments Z.mul !_ !_.

  Lemma quot_sgn_nonneg a b : 0 <= Z.sgn (Z.quot a b) * Z.sgn a * Z.sgn b.
  Proof.
    rewrite quot_div_full, !Z.sgn_mul, !Z.sgn_sgn.
    set (d := Z.abs a / Z.abs b).
    destruct a, b; simpl; try (subst d; simpl; omega);
      try rewrite (Z.mul_opp_l 1);
      do 2 try rewrite (Z.mul_opp_r _ 1);
      rewrite ?Z.mul_1_l, ?Z.mul_1_r, ?Z.opp_involutive;
      apply Z.div_abs_sgn_nonneg.
  Qed.

  Lemma quot_nonneg_same_sgn a b : Z.sgn a = Z.sgn b -> 0 <= Z.quot a b.
  Proof.
    intro H.
    generalize (quot_sgn_nonneg a b); rewrite H.
    rewrite <- Z.mul_assoc, <- Z.sgn_mul.
    destruct (Z_zerop b); [ subst; destruct a; unfold Z.quot; simpl in *; congruence | ].
    rewrite (Z.sgn_pos (_ * _)) by nia.
    intro; apply Z.sgn_nonneg; omega.
  Qed.

  Lemma mul_quot_eq_full a m : m <> 0 -> m * (Z.quot a m) = a - a mod (Z.abs m * Z.sgn a).
  Proof.
    intro Hm.
    assert (0 <> m * m) by (intro; apply Hm; nia).
    assert (0 < m * m) by nia.
    assert (0 <> Z.abs m) by (destruct m; simpl in *; try congruence).
    rewrite quot_div_full.
    rewrite <- (Z.abs_sgn m) at 1.
    transitivity ((Z.sgn m * Z.sgn m) * Z.sgn a * (Z.abs m * (Z.abs a / Z.abs m))); [ nia | ].
    rewrite <- Z.sgn_mul, Z.sgn_pos, Z.mul_1_l, Z.mul_div_eq_full by omega.
    rewrite Z.mul_sub_distr_l.
    rewrite Z.mul_comm, Z.abs_sgn.
    destruct a; simpl Z.sgn; simpl Z.abs; autorewrite with zsimplify_const; [ reflexivity | reflexivity | ].
    repeat match goal with |- context[-1 * ?x] => replace (-1 * x) with (-x) by omega end.
    repeat match goal with |- context[?x * -1] => replace (x * -1) with (-x) by omega end.
    rewrite <- Zmod_opp_opp; simpl Z.opp.
    reflexivity.
  Qed.

  Lemma quot_sub_sgn a : Z.quot (a - Z.sgn a) a = 0.
  Proof.
    rewrite quot_div_full.
    destruct (Z_zerop a); subst; [ lia | ].
    rewrite Z.div_small; lia.
  Qed.

  Lemma quot_small_abs a b : 0 <= Z.abs a < Z.abs b -> Z.quot a b = 0.
  Proof.
    intros; rewrite Z.quot_small_iff by lia; lia.
  Qed.

  Lemma quot_add_sub_sgn_small a b : b <> 0 -> Z.sgn a = Z.sgn b -> Z.quot (a + b - Z.sgn b) b = Z.quot (a - Z.sgn b) b + 1.
  Proof.
    destruct (Z_zerop a), (Z_zerop b), (Z_lt_le_dec a 0), (Z_lt_le_dec b 0), (Z_lt_le_dec 1 (Z.abs a));
      subst;
      try lia;
      rewrite !Z.quot_div_full;
      try rewrite (Z.sgn_neg a) by omega;
      try rewrite (Z.sgn_neg b) by omega;
      repeat first [ reflexivity
                   | rewrite Z.sgn_neg by lia
                   | rewrite Z.sgn_pos by lia
                   | rewrite Z.abs_eq by lia
                   | rewrite Z.abs_neq by lia
                   | rewrite !Z.mul_opp_l
                   | rewrite Z.abs_opp in *
                   | rewrite Z.abs_eq in * by omega
                   | match goal with
                     | [ |- context[-1 * ?x] ]
                       => replace (-1 * x) with (-x) by omega
                     | [ |- context[?x * -1] ]
                       => replace (x * -1) with (-x) by omega
                     | [ |- context[-?x - ?y] ]
                       => replace (-x - y) with (-(x + y)) by omega
                     | [ |- context[-?x + - ?y] ]
                       => replace (-x + - y) with (-(x + y)) by omega
                     | [ |- context[(?a + ?b + ?c) / ?b] ]
                       => replace (a + b + c) with (((a + c) + b * 1)) by lia; rewrite Z.div_add' by omega
                     | [ |- context[(?a + ?b - ?c) / ?b] ]
                       => replace (a + b - c) with (((a - c) + b * 1)) by lia; rewrite Z.div_add' by omega
                     end
                   | progress intros
                   | progress Z.replace_all_neg_with_pos
                   | progress autorewrite with zsimplify ].
  Qed.
End Z.
