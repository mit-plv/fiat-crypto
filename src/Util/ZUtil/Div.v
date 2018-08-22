Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Crypto.Util.ZUtil.Tactics.CompareToSgn.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Le.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul; auto. Qed.
  Hint Rewrite div_mul' using zutil_arith : zsimplify.

  Local Ltac replace_to_const c :=
    repeat match goal with
           | [ H : ?x = ?x |- _ ] => clear H
           | [ H : ?x = c, H' : context[?x] |- _ ] => rewrite H in H'
           | [ H : c = ?x, H' : context[?x] |- _ ] => rewrite <- H in H'
           | [ H : ?x = c |- context[?x] ] => rewrite H
           | [ H : c = ?x |- context[?x] ] => rewrite <- H
           end.

  Lemma lt_div_0 n m : n / m < 0 <-> ((n < 0 < m \/ m < 0 < n) /\ 0 < -(n / m)).
  Proof.
    Z.compare_to_sgn; rewrite Z.sgn_opp; simpl.
    pose proof (Zdiv_sgn n m) as H.
    pose proof (Z.sgn_spec (n / m)) as H'.
    repeat first [ progress intuition auto
                 | progress simpl in *
                 | congruence
                 | lia
                 | progress replace_to_const (-1)
                 | progress replace_to_const 0
                 | progress replace_to_const 1
                 | match goal with
                   | [ x : Z |- _ ] => destruct x
                   end ].
  Qed.

  Lemma div_add' a b c : c <> 0 -> (a + c * b) / c = a / c + b.
  Proof. intro; rewrite <- Z.div_add, (Z.mul_comm c); try lia. Qed.

  Lemma div_add_l' a b c : b <> 0 -> (b * a + c) / b = a + c / b.
  Proof. intro; rewrite <- Z.div_add_l, (Z.mul_comm b); lia. Qed.

  Hint Rewrite div_add_l' div_add' using zutil_arith : zsimplify.

  Lemma div_sub a b c : c <> 0 -> (a - b * c) / c = a / c - b.
  Proof. intros; rewrite <- !Z.add_opp_r, <- Z.div_add by lia; apply f_equal2; lia. Qed.

  Lemma div_sub' a b c : c <> 0 -> (a - c * b) / c = a / c - b.
  Proof. intro; rewrite <- div_sub, (Z.mul_comm c); try lia. Qed.

  Hint Rewrite div_sub div_sub' using zutil_arith : zsimplify.

  Lemma div_add_sub_l a b c d : b <> 0 -> (a * b + c - d) / b = a + (c - d) / b.
  Proof. rewrite <- Z.add_sub_assoc; apply Z.div_add_l. Qed.

  Lemma div_add_sub_l' a b c d : b <> 0 -> (b * a + c - d) / b = a + (c - d) / b.
  Proof. rewrite <- Z.add_sub_assoc; apply Z.div_add_l'. Qed.

  Lemma div_add_sub a b c d : c <> 0 -> (a + b * c - d) / c = (a - d) / c + b.
  Proof. rewrite (Z.add_comm _ (_ * _)), (Z.add_comm (_ / _)); apply Z.div_add_sub_l. Qed.

  Lemma div_add_sub' a b c d : c <> 0 -> (a + c * b - d) / c = (a - d) / c + b.
  Proof. rewrite (Z.add_comm _ (_ * _)), (Z.add_comm (_ / _)); apply Z.div_add_sub_l'. Qed.

  Hint Rewrite Z.div_add_sub Z.div_add_sub' Z.div_add_sub_l Z.div_add_sub_l' using zutil_arith : zsimplify.

  Lemma div_mul_skip a b k : 0 < b -> 0 < k -> a * b / k / b = a / k.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm k), <- Z.div_div by lia.
    autorewrite with zsimplify. reflexivity.
  Qed.

  Lemma div_mul_skip' a b k : 0 < b -> 0 < k -> b * a / k / b = a / k.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm k), <- Z.div_div by lia.
    autorewrite with zsimplify; reflexivity.
  Qed.

  Hint Rewrite Z.div_mul_skip Z.div_mul_skip' using zutil_arith : zsimplify.

  Lemma div_mul_skip_pow base e0 e1 x y : 0 < y -> 0 < base -> 0 <= e1 <= e0 -> x * base^e0 / y / base^e1 = x * base^(e0 - e1) / y.
  Proof.
    intros.
    assert (0 < base^e1) by auto with zarith.
    replace (base^e0) with (base^(e0 - e1) * base^e1) by (autorewrite with pull_Zpow zsimplify; reflexivity).
    rewrite !Z.mul_assoc.
    autorewrite with zsimplify; lia.
  Qed.
  Hint Rewrite div_mul_skip_pow using zutil_arith : zsimplify.

  Lemma div_mul_skip_pow' base e0 e1 x y : 0 < y -> 0 < base -> 0 <= e1 <= e0 -> base^e0 * x / y / base^e1 = base^(e0 - e1) * x / y.
  Proof.
    intros.
    rewrite (Z.mul_comm (base^e0) x), div_mul_skip_pow by lia.
    auto using f_equal2 with lia.
  Qed.
  Hint Rewrite div_mul_skip_pow' using zutil_arith : zsimplify.

  Lemma div_le_mono_nonneg a b c : 0 <= c -> a <= b -> a / c <= b / c.
  Proof.
    destruct (Z_zerop c).
    { subst; simpl; autorewrite with zsimplify; reflexivity. }
    { intros; apply Z.div_le_mono; omega. }
  Qed.
  Hint Resolve div_le_mono_nonneg : zarith.

  Lemma div_le_mono_pow_pos a b c e : a <= b -> a / Z.pos c ^ e <= b / Z.pos c ^ e.
  Proof. auto with zarith. Qed.

  Lemma div_nonneg a b : 0 <= a -> 0 <= b -> 0 <= a / b.
  Proof.
    destruct (Z_zerop b); subst; rewrite ?Zdiv_0_r; [ reflexivity | ].
    intros; apply Z.div_pos; omega.
  Qed.
  Hint Resolve div_nonneg : zarith.

  Lemma div_add_exact x y d : d <> 0 -> x mod d = 0 -> (x + y) / d = x / d + y / d.
  Proof.
    intros; rewrite (Z_div_exact_full_2 x d) at 1 by assumption.
    rewrite Z.div_add_l' by assumption; lia.
  Qed.
  Hint Rewrite div_add_exact using zutil_arith : zsimplify.

  Lemma Z_divide_div_mul_exact' a b c : b <> 0 -> (b | a) -> a * c / b = c * (a / b).
  Proof. intros. rewrite Z.mul_comm. auto using Z.divide_div_mul_exact. Qed.

  Lemma div_sub_mod_exact a b : b <> 0 -> a / b = (a - a mod b) / b.
  Proof.
    intro.
    rewrite (Z.div_mod a b) at 2 by lia.
    autorewrite with zsimplify.
    reflexivity.
  Qed.

  Lemma div_sub_mod_cond x y d
    : d <> 0
      -> (x - y) / d
         = x / d + ((x mod d - y) / d).
  Proof. clear.
         intro.
         replace (x - y) with ((x - x mod d) + (x mod d - y)) by lia.
         rewrite Z.div_add_exact by (autorewrite with pull_Zmod zsimplify; auto).
         rewrite <- Z.div_sub_mod_exact by lia; lia.
  Qed.
  Hint Resolve div_sub_mod_cond : zarith.

  Lemma div_add_mod_cond_l : forall x y d, d <> 0 -> (x + y) / d = (x mod d + y) / d + x / d.
  Proof.
    intros. replace (x + y) with ((x - x mod d) + (x mod d + y)) by lia.
    rewrite Z.div_add_exact by (autorewrite with pull_Zmod zsimplify; auto).
    rewrite <- Z.div_sub_mod_exact by lia; lia.
  Qed.

  Lemma div_add_mod_cond_r : forall x y d, d <> 0 -> (x + y) / d = (x + y mod d) / d + y / d.
  Proof.
    intros. rewrite Z.add_comm, div_add_mod_cond_l by auto. repeat (f_equal; try ring).
  Qed.

  Lemma div_le_zero x y : 0 < y -> x / y <= 0 -> x < y.
  Proof.
    clear. intros.
    apply Z.nle_gt; intro.
    pose proof (Z.div_str_pos x y ltac:(lia)). lia.
  Qed.

  Lemma div_between_full n a b :
    0 < b -> n * b <= a < (1 + n) * b ->
    a / b = n.
  Proof.
    intros.
    pose proof (Z.div_le_lower_bound a b n ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound a b (n+1) ltac:(lia) ltac:(lia)).
    lia.
  Qed.

  Lemma mod_small_n_neg n a b : n < 0 -> 0 < b -> n * b <= a < (1 + n) * b ->
                                a mod b = a - n * b.
  Proof.
    intros. rewrite Z.mod_eq, div_between_full with (n:=n) by omega. ring.
  Qed.

  Lemma div_div_comm : forall x y z,  0 < y -> 0 < z -> x / y / z = x / z / y.
  Proof.
    intros; rewrite !Z.div_div by omega.
    f_equal; ring.
  Qed.

  Lemma div_lt_upper_bound' a b q : 0 < b -> a < q * b -> a / b < q.
  Proof. intros; apply Z.div_lt_upper_bound; nia. Qed.
  Hint Resolve div_lt_upper_bound' : zarith.

  Lemma div_cross_le_abs a b c' d : c' <> 0 -> d <> 0 -> a * Z.sgn c' * Z.abs d <= b * Z.sgn d * Z.abs c' -> a / c' <= b / d.
  Proof.
    clear.
    destruct c', d; cbn [Z.abs Z.sgn];
      rewrite ?Zdiv_0_r, ?Z.mul_0_r, ?Z.mul_0_l, ?Z.mul_1_l, ?Z.mul_1_r;
      try lia; intros ?? H;
        Z.div_mod_to_quot_rem_in_goal;
        subst.
    all: repeat match goal with
                | [ H : context[_ * -1] |- _ ] => rewrite (Z.mul_add_distr_r _ _ (-1)), <- ?(Z.mul_comm (-1)), ?Z.mul_assoc in H
                | [ H : context[-1 * _] |- _ ] => rewrite (Z.mul_add_distr_l (-1)), <- ?(Z.mul_comm (-1)), ?Z.mul_assoc in H
                | [ H : context[-1 * Z.neg ?x] |- _ ] => rewrite (Z.mul_comm (-1) (Z.neg x)), <- Z.opp_eq_mul_m1 in H
                | [ H : context[-1 * ?x] |- _ ] => rewrite (Z.mul_comm (-1) x), <- Z.opp_eq_mul_m1 in H
                | [ H : context[-Z.neg _] |- _ ] => cbn [Z.opp] in H
                end.
    all:lazymatch goal with
        | [ H : (Z.pos ?p * ?q + ?r) * Z.pos ?p' <= (Z.pos ?p' * ?q' + ?r') * Z.pos ?p |- _ ]
          => let H' := fresh in
             assert (H' : q <= q' + (r' * Z.pos p - r * Z.pos p') / (Z.pos p * Z.pos p')) by (Z.div_mod_to_quot_rem_in_goal; nia);
               revert H'
        end.
    all:Z.div_mod_to_quot_rem_in_goal; nia.
  Qed.

  Lemma div_positive_gt_0 : forall a b, a > 0 -> b > 0 -> a mod b = 0 ->
    a / b > 0.
  Proof.
    intros; rewrite Z.gt_lt_iff.
    apply Z.div_str_pos.
    split; intuition auto with omega.
    apply Z.divide_pos_le; try (apply Zmod_divide); omega.
  Qed.

  Lemma div_opp_l_complete a b (Hb : b <> 0) : -a/b = -(a/b) - (if Z_zerop (a mod b) then 0 else 1).
  Proof.
    destruct (Z_zerop (a mod b)); autorewrite with zsimplify push_Zopp; reflexivity.
  Qed.

  Lemma div_opp_l_complete' a b (Hb : b <> 0) : -(a/b) = -a/b + (if Z_zerop (a mod b) then 0 else 1).
  Proof.
    destruct (Z_zerop (a mod b)); autorewrite with zsimplify pull_Zopp; lia.
  Qed.

  Hint Rewrite Z.div_opp_l_complete using zutil_arith : pull_Zopp.
  Hint Rewrite Z.div_opp_l_complete' using zutil_arith : push_Zopp.

  Lemma div_opp a : a <> 0 -> -a / a = -1.
  Proof.
    intros; autorewrite with pull_Zopp zsimplify; lia.
  Qed.

  Hint Rewrite Z.div_opp using zutil_arith : zsimplify.

  Lemma div_sub_1_0 x : x > 0 -> (x - 1) / x = 0.
  Proof. auto with zarith lia. Qed.

  Hint Rewrite div_sub_1_0 using zutil_arith : zsimplify.

  Lemma div_same' a b : b <> 0 -> a = b -> a / b = 1.
  Proof.
    intros; subst; auto with zarith.
  Qed.
  Hint Resolve div_same' : zarith.

  Lemma div_opp_r a b : a / (-b) = ((-a) / b).
  Proof. Z.div_mod_to_quot_rem; nia. Qed.
  Hint Resolve div_opp_r : zarith.

  Lemma div_floor : forall a b c, 0 < b -> a < b * (Z.succ c) -> a / b <= c.
  Proof.
    intros.
    apply Z.lt_succ_r.
    apply Z.div_lt_upper_bound; try omega.
  Qed.
End Z.
