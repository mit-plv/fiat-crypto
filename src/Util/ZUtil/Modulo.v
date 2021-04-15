Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.ZArith.Znumtheory Coq.ZArith.Zpow_facts.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Divide.
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
      rewrite Z.pow_add_r, Z.pow_1_r by lia; auto using Z.mod_add_l.
  Qed.

  Lemma mod_exp_0 : forall a x m, x > 0 -> m > 1 -> a mod m = 0 ->
    a ^ x mod m = 0.
  Proof.
    intros a x m H H0 H1.
    replace x with (Z.of_nat (Z.to_nat x)) in * by (apply Z2Nat.id; lia).
    induction (Z.to_nat x). {
      simpl in *; lia.
    } {
      rewrite Nat2Z.inj_succ in *.
      rewrite Z.pow_succ_r by lia.
      rewrite Z.mul_mod by lia.
      case_eq n; intros. {
        subst. simpl.
        rewrite Zmod_1_l by lia.
        rewrite H1.
        apply Zmod_0_l.
      } {
        subst.
        rewrite IHn by (rewrite Nat2Z.inj_succ in *; lia).
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
      rewrite !Z2Nat.id in H by lia.
    rewrite <-H by (change 0%nat with (Z.to_nat 0); rewrite Z2Nat.inj_iff; lia).
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

  Local Lemma mod_pull_div_helper a b c X
        (HX : forall a b c d e f g,
            X a b c d e f g = if a =? 0 then c else 0)
    : 0 <> b
      -> 0 <> c
      -> (a / b) mod c
         = (a mod (c * b)) / b
           + if c <? 0 then - X ((a / b) mod c) (a mod (c * b)) ((a mod (c * b)) / b) a b c (a / b) else 0.
  Proof.
    intros; break_match; Z.ltb_to_lt; rewrite ?Z.sub_0_r, ?Z.add_0_r;
      assert (0 <> c * b) by nia; Z.div_mod_to_quot_rem_in_goal; subst;
        destruct_head'_or; destruct_head'_and;
          try assert (b < 0) by lia;
          try assert (c < 0) by lia;
          Z.replace_all_neg_with_pos;
          try match goal with
              | [ H : ?c * ?b * ?q1 + ?r1 = ?b * (?c * ?q2 + _) + _ |- _ ]
                => assert (q1 = q2) by nia; progress subst
              end;
          rewrite ?HX; clear HX X;
          try nia;
          repeat match goal with
                 | [ |- - ?x = ?y ] => is_var y; assert (y <= 0) by nia; Z.replace_all_neg_with_pos
                 | [ |- - ?x = ?y + -_ ] => is_var y; assert (y <= 0) by nia; Z.replace_all_neg_with_pos
                 | [ H : -?x + (-?y + ?z) = -?w + ?v |- _ ]
                   => assert (x + (y + -z) = w + -v) by lia; clear H
                 | [ H : ?c * ?b * ?q1 + (?b * ?q2 + ?r) = ?b * (?c * ?q1' + ?q2') + ?r' |- _ ]
                   => assert (c * q1 + q2 = c * q1' + q2') by nia;
                        assert (r = r') by nia;
                        clear H
                 | [ H : -?x < -?y + ?z |- _ ] => assert (y + -z < x) by lia; clear H
                 | [ H : -?x + ?y <= 0 |- _ ] => assert (0 <= x + -y) by lia; clear H
                 | _ => progress Z.clean_neg
                 | _ => progress subst
                 end.
    all:match goal with
        | [ H : ?c * ?q + ?r = ?c * ?q' + ?r' |- _ ]
          => first [ constr_eq q q'; assert (r = r') by nia; clear H
                   | assert (q = q') by nia; assert (r = r') by nia; clear H
                   | lazymatch goal with
                     | [ H' : r' < c |- _ ]
                       => destruct (Z_dec' r c) as [[?|?]|?]
                     | [ H' : r < c |- _ ]
                       => destruct (Z_dec' r' c) as [[?|?]|?]
                     end;
                     subst;
                     [ assert (q = q') by nia; assert (r = r') by nia; clear H
                     | nia
                     | first [ assert (1 + q = q') by nia | assert (q = 1 + q') by nia ];
                       first [ assert (r' = 0) by nia | assert (r = 0) by nia ] ] ]
        end.
    all:try lia.
    all:break_match; Z.ltb_to_lt; lia.
  Qed.

  Lemma mod_pull_div_full a b c
    : (a / b) mod c
      = if ((c <? 0) && ((a / b) mod c =? 0))%bool
        then 0
        else (a mod (c * b)) / b.
  Proof.
    destruct (Z_zerop b), (Z_zerop c); subst;
      autorewrite with zsimplify; try reflexivity.
    { break_match; Z.ltb_to_lt; lia. }
    { erewrite mod_pull_div_helper at 1 by (lia || reflexivity); cbv beta.
      destruct (c <? 0) eqn:?; simpl; [ | lia ].
      break_innermost_match; lia. }
  Qed.

  Lemma mod_pull_div a b c
    : 0 <= c -> (a / b) mod c = a mod (c * b) / b.
  Proof. rewrite mod_pull_div_full; destruct (c <? 0) eqn:?; Z.ltb_to_lt; simpl; lia. Qed.

  Lemma small_mod_eq a b n: a mod n = b mod n -> 0 <= a < n -> a = b mod n.
  Proof. intros; rewrite <-(Z.mod_small a n); auto. Qed.

  Lemma mod_bound_min_max l x u d (H : l <= x <= u)
    : (if l / d =? u / d then Z.min (l mod d) (u mod d) else Z.min 0 (d + 1))
      <= x mod d
      <= if l / d =? u / d then Z.max (l mod d) (u mod d) else Z.max 0 (d - 1).
  Proof.
    destruct (Z_dec d 0) as [ [?|?] | ? ];
      try solve [ subst; autorewrite with zsimplify; simpl; split; reflexivity
                | repeat first [ progress Z.div_mod_to_quot_rem_in_goal
                               | progress subst
                               | progress break_innermost_match
                               | progress Z.ltb_to_lt
                               | progress destruct_head'_or
                               | progress destruct_head'_and
                               | progress apply Z.min_case_strong
                               | progress apply Z.max_case_strong
                               | progress intros
                               | lia
                               | match goal with
                                 | [ H : ?x <= ?y, H' : ?y <= ?x |- _ ] => assert (x = y) by lia; clear H H'
                                 | _ => progress subst
                                 | [ H : ?d * ?q0 + ?r0 = ?d * ?q1 + ?r1 |- _ ]
                                   => assert (q0 = q1) by nia; subst q0
                                 | [ H : ?d * ?q0 + ?r0 <= ?d * ?q1 + ?r1 |- _ ]
                                   => assert (q0 = q1) by nia; subst q0
                                 end ] ].
  Qed.

  Lemma mod_mod_0_0_eq x y : x mod y = 0 -> y mod x = 0 -> x = y \/ x = - y \/ x = 0 \/ y = 0.
  Proof.
    destruct (Z_zerop x), (Z_zerop y); eauto.
    Z.div_mod_to_quot_rem_in_goal; subst.
    rewrite ?Z.add_0_r in *.
    match goal with
    | [ H : ?x = ?x * ?q * ?q' |- _ ]
      => assert (q * q' = 1) by nia;
          destruct_head'_or;
          first [ assert (q < 0) by nia
                | assert (0 < q) by nia ];
          first [ assert (q' < 0) by nia
                | assert (0 < q') by nia ]
    end;
      nia.
  Qed.
  Lemma mod_mod_0_0_eq_pos x y : 0 < x -> 0 < y -> x mod y = 0 -> y mod x = 0 -> x = y.
  Proof. intros ?? H0 H1; pose proof (mod_mod_0_0_eq x y H0 H1); lia. Qed.
  Lemma mod_mod_trans x y z : y <> 0 -> x mod y = 0 -> y mod z = 0 -> x mod z = 0.
  Proof.
    intros Hy. rewrite (Zmod_eq_full x y Hy). intros Hx Hyz.
    replace x with (x / y * y) by lia. now rewrite Zmult_mod, Hyz, Z.mul_0_r.
  Qed.

  Lemma mod_opp_r a b : a mod (-b) = -((-a) mod b).
  Proof. pose proof (Z.div_opp_r a b); Z.div_mod_to_quot_rem; nia. Qed.
  Hint Resolve mod_opp_r : zarith.

  Lemma mod_same_pow : forall a b c, 0 <= c <= b -> a ^ b mod a ^ c = 0.
  Proof.
    intros a b c H.
    replace b with (b - c + c) by ring.
    rewrite Z.pow_add_r by lia.
    apply Z_mod_mult.
  Qed.
  Hint Rewrite mod_same_pow using zutil_arith : zsimplify.
  Hint Resolve mod_same_pow : zarith.

  Lemma mod_opp_l_z_iff a b (H : b <> 0) : a mod b = 0 <-> (-a) mod b = 0.
  Proof.
    split; intro H'; apply Z.mod_opp_l_z in H'; rewrite ?Z.opp_involutive in H'; assumption.
  Qed.
  Hint Rewrite <- mod_opp_l_z_iff using zutil_arith : zsimplify.

  Lemma mod_small_sym a b : 0 <= a < b -> a = a mod b.
  Proof. intros; symmetry; apply Z.mod_small; assumption. Qed.
  Hint Resolve mod_small_sym : zarith.

  Lemma mod_eq_le_to_eq a b : 0 < a <= b -> a mod b = 0 -> a = b.
  Proof. pose proof (Z.mod_eq_le_div_1 a b); intros; Z.div_mod_to_quot_rem; nia. Qed.
  Hint Resolve mod_eq_le_to_eq : zarith.

  Lemma mod_neq_0_le_to_neq a b : a mod b <> 0 -> a <> b.
  Proof. repeat intro; subst; autorewrite with zsimplify in *; lia. Qed.
  Hint Resolve mod_neq_0_le_to_neq : zarith.

  Lemma div_mod' a b : b <> 0 -> a = (a / b) * b + a mod b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod' using zutil_arith : zsimplify.

  Lemma div_mod'' a b : b <> 0 -> a = a mod b + b * (a / b).
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod'' using zutil_arith : zsimplify.

  Lemma div_mod''' a b : b <> 0 -> a = a mod b + (a / b) * b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod''' using zutil_arith : zsimplify.

  Lemma sub_mod_mod_0 x d : (x - x mod d) mod d = 0.
  Proof.
    destruct (Z_zerop d); subst; push_Zmod; autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Resolve sub_mod_mod_0 : zarith.
  Hint Rewrite sub_mod_mod_0 : zsimplify.

  Lemma mod_small_n n a b : 0 <= n -> b <> 0 -> n * b <= a < (1 + n) * b -> a mod b = a - n * b.
  Proof. intros; erewrite Zmod_eq_full, Z.div_between by eassumption. reflexivity. Qed.
  Hint Rewrite mod_small_n using zutil_arith : zsimplify.

  Lemma mod_small_1 a b : b <> 0 -> b <= a < 2 * b -> a mod b = a - b.
  Proof. intros; rewrite (mod_small_n 1) by lia; lia. Qed.
  Hint Rewrite mod_small_1 using zutil_arith : zsimplify.

  Lemma mod_opp_small a m : 0 < a <= m -> (-a) mod m = m - a.
  Proof. intros; symmetry; apply Zmod_unique with (-1); lia. Qed.

  Lemma mod_neg_small a m : -m <= a < 0 -> a mod m = m + a.
  Proof. intros; symmetry; apply Zmod_unique with (-1); lia. Qed.

  Lemma mod_small_n_if n a b : 0 <= n -> b <> 0 -> n * b <= a < (2 + n) * b -> a mod b = a - (if (1 + n) * b <=? a then (1 + n) else n) * b.
  Proof. intros; erewrite Zmod_eq_full, Z.div_between_if by eassumption; autorewrite with zsimplify_const. reflexivity. Qed.

  Lemma mod_small_0_if a b : b <> 0 -> 0 <= a < 2 * b -> a mod b = a - if b <=? a then b else 0.
  Proof. intros; rewrite (mod_small_n_if 0) by lia; autorewrite with zsimplify_const. break_match; lia. Qed.

  Lemma mul_mod_distr_r_full a b c : (a * c) mod (b * c) = (a mod b * c).
  Proof.
    destruct (Z_zerop b); [ | destruct (Z_zerop c) ]; subst;
      autorewrite with zsimplify; auto using Z.mul_mod_distr_r.
  Qed.

  Lemma mul_mod_distr_l_full a b c : (c * a) mod (c * b) = c * (a mod b).
  Proof.
    destruct (Z_zerop b); [ | destruct (Z_zerop c) ]; subst;
      autorewrite with zsimplify; auto using Z.mul_mod_distr_l.
  Qed.

  Lemma lt_mul_2_mod_sub : forall a b, b <> 0 -> b <= a < 2 * b -> a mod b = a - b.
  Proof.
    intros a b H H0.
    replace (a mod b) with ((1 * b + (a - b)) mod b) by (f_equal; ring).
    rewrite Z.mod_add_l by auto.
    apply Z.mod_small.
    lia.
  Qed.

  Lemma mod_pow_r_split x b e1 e2 : 0 <= b -> 0 <= e1 <= e2 -> x mod b^e2 = (x mod b^e1) + (b^e1) * ((x / b^e1) mod b^(e2-e1)).
  Proof.
    destruct (Z_zerop b).
    { destruct (Z_zerop e1), (Z_zerop e2), (Z.eq_dec e1 e2); subst; intros; cbn; autorewrite with zsimplify_fast; destruct x; lia. }
    intros.
    replace (b^e2) with (b^e1 * b^(e2 - e1)) by (autorewrite with pull_Zpow; f_equal; lia).
    rewrite Z.rem_mul_r by auto with zarith.
    reflexivity.
  Qed.

  Lemma opp_mod2 a : a mod 2 = - a mod 2.
  Proof. rewrite !Zmod_odd, Z.odd_opp; reflexivity. Qed.
  
  Lemma mod_pow_same_base_larger a b n m :
    0 <= n < m -> 0 < b ->
    (a mod (b^n)) mod (b^m) = a mod b^n.
  Proof.
    intros.
    pose proof Z.mod_pos_bound a (b^n) ltac:(auto with zarith).
    assert (b^n <= b^m) by auto with zarith.
    apply Z.mod_small. auto with zarith.
  Qed.

  Lemma mod_pow_same_base_smaller a b n m :
    0 <= m <= n -> 0 < b ->
    (a mod (b^n)) mod (b^m) = a mod b^m.
  Proof.
    intros. replace n with (m+(n-m)) by lia.
    rewrite Z.pow_add_r, Z.rem_mul_r by auto with zarith.
    push_Zmod; pull_Zmod.
    autorewrite with zsimplify_fast; reflexivity.
  Qed.

  (* Useful lemma for add-get-carry patterns.
     This expression performs a bitwise or. In terms of bit ranges,
       b...a + a...c << a-b = b...c *)
  Lemma add_div_pow2 x a b :
    0 <= b <= a ->
    (x mod (2 ^ a)) / 2 ^ b + x / 2 ^ a * 2 ^ (a - b)
    = x / 2 ^ b.
  Proof.
    intros. rewrite Z.pow_sub_r by auto with zarith.
    rewrite <-Z.divide_div_mul_exact
      by auto using Z.divide_pow_le with zarith.
    rewrite <-Z.div_add by auto with zarith.
    rewrite Z.mul_div_eq', Z.mul_mod, Z.mod_same_pow by auto with zarith.
    autorewrite with zsimplify.
    Z.div_mod_to_quot_rem; nia.
  Qed.
End Z.
