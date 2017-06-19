Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.CompareToSgn.
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
End Z.
