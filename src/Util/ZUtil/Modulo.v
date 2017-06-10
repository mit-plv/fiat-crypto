Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.ZArith.Znumtheory Coq.ZArith.Zpow_facts.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Local Open Scope Z_scope.

Module Z.
  Lemma elim_mod : forall a b m, a = b -> a mod m = b mod m.
  Proof. intros; subst; auto. Qed.
  Hint Resolve elim_mod : zarith.

  Lemma mod_add_full : forall a b c, (a + b * c) mod c = a mod c.
  Proof. intros a b c; destruct (Z_zerop c); try subst; autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_full : zsimplify.

  Lemma mod_add_l_full : forall a b c, (a * b + c) mod b = c mod b.
  Proof. intros a b c; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_l_full : zsimplify.

  Lemma mod_add'_full : forall a b c, (a + b * c) mod b = a mod b.
  Proof. intros a b c; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l'_full : forall a b c, (a * b + c) mod a = c mod a.
  Proof. intros a b c; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add'_full mod_add_l'_full : zsimplify.

  Lemma mod_add_l : forall a b c, b <> 0 -> (a * b + c) mod b = c mod b.
  Proof. intros a b c H; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.

  Lemma mod_add' : forall a b c, b <> 0 -> (a + b * c) mod b = a mod b.
  Proof. intros a b c H; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l' : forall a b c, a <> 0 -> (a * b + c) mod a = c mod a.
  Proof. intros a b c H; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.

  Lemma add_pow_mod_l : forall a b c, a <> 0 -> 0 < b ->
                                      ((a ^ b) + c) mod a = c mod a.
  Proof.
    intros a b c H H0; replace b with (b - 1 + 1) by ring;
      rewrite Z.pow_add_r, Z.pow_1_r by omega; auto using Z.mod_add_l.
  Qed.

  Lemma mod_exp_0 : forall a x m, x > 0 -> m > 1 -> a mod m = 0 ->
    a ^ x mod m = 0.
  Proof.
    intros a x m H H0 H1.
    replace x with (Z.of_nat (Z.to_nat x)) in * by (apply Z2Nat.id; omega).
    induction (Z.to_nat x). {
      simpl in *; omega.
    } {
      rewrite Nat2Z.inj_succ in *.
      rewrite Z.pow_succ_r by omega.
      rewrite Z.mul_mod by omega.
      case_eq n; intros. {
        subst. simpl.
        rewrite Zmod_1_l by omega.
        rewrite H1.
        apply Zmod_0_l.
      } {
        subst.
        rewrite IHn by (rewrite Nat2Z.inj_succ in *; omega).
        rewrite H1.
        auto.
      }
    }
  Qed.

  Lemma mod_pow : forall (a m b : Z), (0 <= b) -> (m <> 0) ->
      a ^ b mod m = (a mod m) ^ b mod m.
  Proof.
    intros a m b H H0; rewrite <- (Z2Nat.id b) by auto.
    induction (Z.to_nat b) as [|n IHn]; auto.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite Z.mul_mod by auto.
    rewrite (Z.mul_mod (a mod m) ((a mod m) ^ Z.of_nat n) m) by auto.
    rewrite <- IHn by auto.
    rewrite Z.mod_mod by auto.
    reflexivity.
  Qed.

  Lemma mod_to_nat x m (Hm:(0 < m)%Z) (Hx:(0 <= x)%Z) : (Z.to_nat x mod Z.to_nat m = Z.to_nat (x mod m))%nat.
    pose proof Zdiv.mod_Zmod (Z.to_nat x) (Z.to_nat m) as H;
      rewrite !Z2Nat.id in H by omega.
    rewrite <-H by (change 0%nat with (Z.to_nat 0); rewrite Z2Nat.inj_iff; omega).
    rewrite !Nat2Z.id; reflexivity.
  Qed.

  Lemma mul_div_eq_full : forall a m, m <> 0 -> m * (a / m) = (a - a mod m).
  Proof.
    intros a m H. rewrite (Z_div_mod_eq_full a m) at 2 by auto. ring.
  Qed.

  Hint Rewrite mul_div_eq_full using zutil_arith : zdiv_to_mod.
  Hint Rewrite <-mul_div_eq_full using zutil_arith : zmod_to_div.

  Lemma f_equal_mul_mod x y x' y' m : x mod m = x' mod m -> y mod m = y' mod m -> (x * y) mod m = (x' * y') mod m.
  Proof.
    intros H0 H1; rewrite Zmult_mod, H0, H1, <- Zmult_mod; reflexivity.
  Qed.
  Hint Resolve f_equal_mul_mod : zarith.

  Lemma f_equal_add_mod x y x' y' m : x mod m = x' mod m -> y mod m = y' mod m -> (x + y) mod m = (x' + y') mod m.
  Proof.
    intros H0 H1; rewrite Zplus_mod, H0, H1, <- Zplus_mod; reflexivity.
  Qed.
  Hint Resolve f_equal_add_mod : zarith.

  Lemma f_equal_opp_mod x x' m : x mod m = x' mod m -> (-x) mod m = (-x') mod m.
  Proof.
    intro H.
    destruct (Z_zerop (x mod m)) as [H'|H'], (Z_zerop (x' mod m)) as [H''|H''];
      try congruence.
    { rewrite !Z_mod_zero_opp_full by assumption; reflexivity. }
    { rewrite Z_mod_nz_opp_full, H, <- Z_mod_nz_opp_full by assumption; reflexivity. }
  Qed.
  Hint Resolve f_equal_opp_mod : zarith.

  Lemma f_equal_sub_mod x y x' y' m : x mod m = x' mod m -> y mod m = y' mod m -> (x - y) mod m = (x' - y') mod m.
  Proof.
    rewrite <- !Z.add_opp_r; auto with zarith.
  Qed.
  Hint Resolve f_equal_sub_mod : zarith.

  Lemma mul_div_eq : forall a m, m > 0 -> m * (a / m) = (a - a mod m).
  Proof.
    intros a m H.
    rewrite (Z_div_mod_eq a m) at 2 by auto.
    ring.
  Qed.

  Lemma mul_div_eq' : (forall a m, m > 0 -> (a / m) * m = (a - a mod m))%Z.
  Proof.
    intros a m H.
    rewrite (Z_div_mod_eq a m) at 2 by auto.
    ring.
  Qed.

  Hint Rewrite mul_div_eq mul_div_eq' using zutil_arith : zdiv_to_mod.
  Hint Rewrite <- mul_div_eq' using zutil_arith : zmod_to_div.

  Lemma mod_div_eq0 : forall a b, 0 < b -> (a mod b) / b = 0.
  Proof.
    intros.
    apply Z.div_small.
    auto using Z.mod_pos_bound.
  Qed.
  Hint Rewrite mod_div_eq0 using zutil_arith : zsimplify.

  Lemma power_mod_full p q n : (p^q) mod n = ((p mod n)^q) mod n.
  Proof.
    destruct (Z_dec' n 0) as [ [H|H] | H]; subst;
      [
      | apply Zpower_mod; assumption
      | rewrite !Zmod_0_r; reflexivity ].
    { revert H.
      rewrite <- (Z.opp_involutive (p^q)),
      <- (Z.opp_involutive ((p mod n)^q)),
      <- (Z.opp_involutive p),
      <- (Z.opp_involutive n).
      generalize (-n); clear n; intros n H.
      rewrite !Zmod_opp_opp.
      rewrite !Z.opp_involutive.
      apply f_equal.
      destruct (Z.Even_or_Odd q).
      { rewrite !Z.pow_opp_even by (assumption || omega).
        destruct (Z.eq_dec (p^q mod n) 0) as [H'|H'], (Z.eq_dec ((-p mod n)^q mod n) 0) as [H''|H''];
          repeat first [ rewrite Z_mod_zero_opp_full by assumption
                       | rewrite Z_mod_nz_opp_full by assumption
                       | reflexivity
                       | rewrite <- Zpower_mod, Z.pow_opp_even in H'' by (assumption || omega); omega
                       | rewrite <- Zpower_mod, Z.pow_opp_even in H'' |- * by (assumption || omega); omega ]. }
      { rewrite Z.pow_opp_odd, !Z.opp_involutive, <- Zpower_mod, Z.pow_opp_odd, ?Z.opp_involutive by (assumption || omega).
        reflexivity. } }
  Qed.

  Lemma mod_bound_min_max l x u d (H : l <= x <= u)
    : (if l / d =? u / d then Z.min (l mod d) (u mod d) else Z.min 0 (d + 1))
      <= x mod d
      <= if l / d =? u / d then Z.max (l mod d) (u mod d) else Z.max 0 (d - 1).
  Proof.
    destruct (Z_dec d 0) as [ [?|?] | ? ];
      try solve [ subst; autorewrite with zsimplify; simpl; split; reflexivity
                | repeat first [ progress Z.div_mod_to_quot_rem
                               | progress subst
                               | progress break_innermost_match
                               | progress Z.ltb_to_lt
                               | progress destruct_head'_or
                               | progress destruct_head'_and
                               | progress apply Z.min_case_strong
                               | progress apply Z.max_case_strong
                               | progress intros
                               | omega
                               | match goal with
                                 | [ H : ?x <= ?y, H' : ?y <= ?x |- _ ] => assert (x = y) by omega; clear H H'
                                 | _ => progress subst
                                 | [ H : ?d * ?q0 + ?r0 = ?d * ?q1 + ?r1 |- _ ]
                                   => assert (q0 = q1) by nia; subst q0
                                 | [ H : ?d * ?q0 + ?r0 <= ?d * ?q1 + ?r1 |- _ ]
                                   => assert (q0 = q1) by nia; subst q0
                                 end ] ].
  Qed.
End Z.
