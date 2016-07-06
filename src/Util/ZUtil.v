Require Import Coq.ZArith.Zpower Coq.ZArith.Znumtheory Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.NatUtil.
Require Import Coq.Lists.List.
Import Nat.
Local Open Scope Z.

Lemma gt_lt_symmetry: forall n m, n > m <-> m < n.
Proof.
  intros; split; omega.
Qed.

Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
Proof.
  intros; omega.
Qed.
Hint Resolve positive_is_nonzero.

Lemma div_positive_gt_0 : forall a b, a > 0 -> b > 0 -> a mod b = 0 ->
  a / b > 0.
Proof.
  intros; rewrite gt_lt_symmetry.
  apply Z.div_str_pos.
  split; intuition.
  apply Z.divide_pos_le; try (apply Zmod_divide); omega.
Qed.

Lemma elim_mod : forall a b m, a = b -> a mod m = b mod m.
Proof.
  intros; subst; auto.
Qed.
Hint Resolve elim_mod.

Lemma mod_mult_plus: forall a b c, (b <> 0) -> (a * b + c) mod b = c mod b.
Proof.
  intros.
  rewrite Zplus_mod.
  rewrite Z.mod_mul; auto; simpl.
  rewrite Zmod_mod; auto.
Qed.

Lemma pos_pow_nat_pos : forall x n,
  Z.pos x ^ Z.of_nat n > 0.
  do 2 (intros; induction n; subst; simpl in *; auto with zarith).
  rewrite <- Pos.add_1_r, Zpower_pos_is_exp.
  apply Zmult_gt_0_compat; auto; reflexivity.
Qed.

Lemma Z_div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  intros. rewrite Z.mul_comm. apply Z.div_mul; auto.
Qed.

Lemma Zgt0_neq0 : forall x, x > 0 -> x <> 0.
  intuition.
Qed.

Lemma pow_Z2N_Zpow : forall a n, 0 <= a ->
  ((Z.to_nat a) ^ n = Z.to_nat (a ^ Z.of_nat n)%Z)%nat.
Proof.
  intros; induction n; try reflexivity.
  rewrite Nat2Z.inj_succ.
  rewrite pow_succ_r by apply le_0_n.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite IHn.
  rewrite Z2Nat.inj_mul; auto using Z.pow_nonneg.
Qed.

Lemma mod_exp_0 : forall a x m, x > 0 -> m > 1 -> a mod m = 0 ->
  a ^ x mod m = 0.
Proof.
  intros.
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
  intros; rewrite <- (Z2Nat.id b) by auto.
  induction (Z.to_nat b); auto.
  rewrite Nat2Z.inj_succ.
  do 2 rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
  rewrite Z.mul_mod by auto.
  rewrite (Z.mul_mod (a mod m) ((a mod m) ^ Z.of_nat n) m) by auto.
  rewrite <- IHn by auto.
  rewrite Z.mod_mod by auto.
  reflexivity.
Qed.

Ltac Zdivide_exists_mul := let k := fresh "k" in
match goal with
| [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H; destruct H as [k H]
| [ |- (?a | ?b) ] => apply Z.mod_divide; try apply Zmod_divides
end; (omega || auto).

Lemma divide_mul_div: forall a b c (a_nonzero : a <> 0) (c_nonzero : c <> 0),
  (a | b * (a / c)) -> (c | a) -> (c | b).
Proof.
  intros ? ? ? ? ? divide_a divide_c_a; do 2 Zdivide_exists_mul.
  rewrite divide_c_a in divide_a.
  rewrite Z_div_mul' in divide_a by auto.
  replace (b * k) with (k * b) in divide_a by ring.
  replace (c * k * k0) with (k * (k0 * c)) in divide_a by ring.
  rewrite Z.mul_cancel_l in divide_a by (intuition; rewrite H in divide_c_a; ring_simplify in divide_a; intuition).
  eapply Zdivide_intro; eauto.
Qed.

Lemma divide2_even_iff : forall n, (2 | n) <-> Z.even n = true.
Proof.
  intro; split. {
    intro divide2_n.
    Zdivide_exists_mul; [ | pose proof (Z.mod_pos_bound n 2); omega].
    rewrite divide2_n.
    apply Z.even_mul.
  } {
    intro n_even.
    pose proof (Zmod_even n).
    rewrite n_even in H.
    apply Zmod_divide; omega || auto.
  }
Qed.

Lemma prime_odd_or_2 : forall p (prime_p : prime p), p = 2 \/ Z.odd p = true.
Proof.
  intros.
  apply Decidable.imp_not_l; try apply Z.eq_decidable.
  intros p_neq2.
  pose proof (Zmod_odd p) as mod_odd.
  destruct (Sumbool.sumbool_of_bool (Z.odd p)) as [? | p_not_odd]; auto.
  rewrite p_not_odd in mod_odd.
  apply Zmod_divides in mod_odd; try omega.
  destruct mod_odd as [c c_id].
  rewrite Z.mul_comm in c_id.
  apply Zdivide_intro in c_id.
  apply prime_divisors in c_id; auto.
  destruct c_id; [omega | destruct H; [omega | destruct H; auto]].
  pose proof (prime_ge_2 p prime_p); omega.
Qed.

Lemma mul_div_eq : (forall a m, m > 0 -> m * (a / m) = (a - a mod m))%Z.
Proof.
  intros.
  rewrite (Z_div_mod_eq a m) at 2 by auto.
  ring.
Qed.

Ltac prime_bound := match goal with
| [ H : prime ?p |- _ ] => pose proof (prime_ge_2 p H); try omega
end.

Lemma Zlt_minus_lt_0 : forall n m, m < n -> 0 < n - m.
Proof.
  intros; omega.
Qed.


Lemma Z_testbit_low : forall n x i, (0 <= i < n) ->
  Z.testbit x i = Z.testbit (Z.land x (Z.ones n)) i.
Proof.
  intros.
  rewrite Z.land_ones by omega.
  symmetry.
  apply Z.mod_pow2_bits_low.
  omega.
Qed.

Lemma Z_testbit_add_shiftl_low : forall i a b n, (0 <= i < n) ->
  Z.testbit (a + Z.shiftl b n) i = Z.testbit a i.
Proof.
  intros.
  erewrite Z_testbit_low; eauto.
  rewrite Z.land_ones, Z.shiftl_mul_pow2 by omega.
  rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 n); omega).
  apply Z.mod_pow2_bits_low.
  omega.
Qed.


Lemma Z_mod_div_eq0 : forall a b, 0 < b -> (a mod b) / b = 0.
Proof.
  intros.
  apply Z.div_small.
  auto using Z.mod_pos_bound.
Qed.

Lemma Z_shiftr_add_shiftl_high : forall n m a b, 0 <= n <= m -> 0 <= a < 2 ^ n ->
  Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr b (m - n).
Proof.
  intros.
  rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by omega.
  replace (2 ^ m) with (2 ^ n * 2 ^ (m - n)) by
    (rewrite <-Z.pow_add_r by omega; f_equal; ring).
  rewrite <-Z.div_div, Z.div_add, (Z.div_small a) ; try solve
    [assumption || apply Z.pow_nonzero || apply Z.pow_pos_nonneg; omega].
  f_equal; ring.
Qed.

Lemma Z_shiftr_add_shiftl_low : forall n m a b, 0 <= m <= n -> 0 <= a < 2 ^ n ->
  Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr a m + Z.shiftr b (m - n).
Proof.
  intros.
  rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2, Z.shiftr_mul_pow2 by omega.
  replace (2 ^ n) with (2 ^ (n - m) * 2 ^ m) by
    (rewrite <-Z.pow_add_r by omega; f_equal; ring).
  rewrite Z.mul_assoc, Z.div_add by (apply Z.pow_nonzero; omega).
  repeat f_equal; ring.
Qed.

Lemma Z_testbit_add_shiftl_high : forall i, (0 <= i) -> forall a b n, (0 <= n <= i) ->
  0 <= a < 2 ^ n ->
  Z.testbit (a + Z.shiftl b n) i = Z.testbit b (i - n).
Proof.
  intros ? ?.
  apply natlike_ind with (x := i); intros; try assumption;
    (destruct (Z_eq_dec 0 n); [ subst; rewrite Z.pow_0_r in *;
     replace a with 0 by omega; f_equal; ring | ]); try omega.
  rewrite <-Z.add_1_r at 1. rewrite <-Z.shiftr_spec by assumption.
  replace (Z.succ x - n) with (x - (n - 1)) by ring.
  rewrite Z_shiftr_add_shiftl_low, <-Z.shiftl_opp_r with (a := b) by omega.
  rewrite <-H1 with (a := Z.shiftr a 1); try omega; [ repeat f_equal; ring | ].
  rewrite Z.shiftr_div_pow2 by omega.
  split; apply Z.div_pos || apply Z.div_lt_upper_bound;
    try solve [rewrite ?Z.pow_1_r; omega].
  rewrite <-Z.pow_add_r by omega.
  replace (1 + (n - 1)) with n by ring; omega.
Qed.

Lemma Z_land_add_land : forall n m a b, (m <= n)%nat ->
  Z.land ((Z.land a (Z.ones (Z.of_nat n))) + (Z.shiftl b (Z.of_nat n))) (Z.ones (Z.of_nat m)) = Z.land a (Z.ones (Z.of_nat m)).
Proof.
  intros.
  rewrite !Z.land_ones by apply Nat2Z.is_nonneg.
  rewrite Z.shiftl_mul_pow2 by apply Nat2Z.is_nonneg.
  replace (b * 2 ^ Z.of_nat n) with
    ((b * 2 ^ Z.of_nat (n - m)) * 2 ^ Z.of_nat m) by
    (rewrite (le_plus_minus m n) at 2; try assumption;
     rewrite Nat2Z.inj_add, Z.pow_add_r by apply Nat2Z.is_nonneg; ring).
  rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat m)); omega).
  symmetry. apply Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; omega).
  rewrite (le_plus_minus m n) by assumption.
  rewrite Nat2Z.inj_add, Z.pow_add_r by apply Nat2Z.is_nonneg.
  apply Z.divide_factor_l.
Qed.

Lemma Z_pow_gt0 : forall a, 0 < a -> forall b, 0 <= b -> 0 < a ^ b.
Proof.
  intros until 1.
  apply natlike_ind; try (simpl; omega).
  intros.
  rewrite Z.pow_succ_r by assumption.
  apply Z.mul_pos_pos; assumption.
Qed.

Lemma div_pow2succ : forall n x, (0 <= x) ->
  n / 2 ^ Z.succ x = Z.div2 (n / 2 ^ x).
Proof.
  intros.
  rewrite Z.pow_succ_r, Z.mul_comm by auto.
  rewrite <- Z.div_div by (try apply Z.pow_nonzero; omega).
  rewrite Zdiv2_div.
  reflexivity.
Qed.

Lemma shiftr_succ : forall n x,
  Z.shiftr n (Z.succ x) = Z.shiftr (Z.shiftr n x) 1.
Proof.
  intros.
  rewrite Z.shiftr_shiftr by omega.
  reflexivity.
Qed.


Definition Z_shiftl_by n a := Z.shiftl a n.

Lemma Z_shiftl_by_mul_pow2 : forall n a, 0 <= n -> Z.mul (2 ^ n) a = Z_shiftl_by n a.
Proof.
  intros.
  unfold Z_shiftl_by.
  rewrite Z.shiftl_mul_pow2 by assumption.
  apply Z.mul_comm.
Qed.

Lemma map_shiftl : forall n l, 0 <= n -> map (Z.mul (2 ^ n)) l = map (Z_shiftl_by n) l.
Proof.
  intros; induction l; auto using Z_shiftl_by_mul_pow2.
  simpl.
  rewrite IHl.
  f_equal.
  apply Z_shiftl_by_mul_pow2.
  assumption.
Qed.

Lemma Z_odd_mod : forall a b, (b <> 0)%Z ->
  Z.odd (a mod b) = if Z.odd b then xorb (Z.odd a) (Z.odd (a / b)) else Z.odd a.
Proof.
  intros.
  rewrite Zmod_eq_full by assumption.
  rewrite <-Z.add_opp_r, Z.odd_add, Z.odd_opp, Z.odd_mul.
  case_eq (Z.odd b); intros; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; auto using Bool.xorb_false_r.
Qed.

Lemma mod_same_pow : forall a b c, 0 <= c <= b -> a ^ b mod a ^ c = 0.
Proof.
  intros.
  replace b with (b - c + c) by ring.
  rewrite Z.pow_add_r by omega.
  apply Z_mod_mult.
Qed.

  Lemma Z_ones_succ : forall x, (0 <= x) ->
    Z.ones (Z.succ x) = 2 ^ x + Z.ones x.
  Proof.
    unfold Z.ones; intros.
    rewrite !Z.shiftl_1_l.
    rewrite Z.add_pred_r.
    apply Z.succ_inj.
    rewrite !Z.succ_pred.
    rewrite Z.pow_succ_r; omega.
  Qed.

  Lemma Z_div_floor : forall a b c, 0 < b -> a < b * (Z.succ c) -> a / b <= c.
  Proof.
    intros.
    apply Z.lt_succ_r.
    apply Z.div_lt_upper_bound; try omega.
  Qed.

  Lemma Z_shiftr_1_r_le : forall a b, a <= b ->
    Z.shiftr a 1 <= Z.shiftr b 1.
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.pow_1_r by omega.
    apply Z.div_le_mono; omega.
  Qed.

  Lemma Z_ones_pred : forall i, 0 < i -> Z.ones (Z.pred i) = Z.shiftr (Z.ones i) 1.
  Proof.
    induction i; [ | | pose proof (Pos2Z.neg_is_neg p) ]; try omega.
    intros.
    unfold Z.ones.
    rewrite !Z.shiftl_1_l, Z.shiftr_div_pow2, <-!Z.sub_1_r, Z.pow_1_r, <-!Z.add_opp_r by omega.
    replace (2 ^ (Z.pos p)) with (2 ^ (Z.pos p - 1)* 2).
    rewrite Z.div_add_l by omega.
    reflexivity.
    change 2 with (2 ^ 1) at 2.
    rewrite <-Z.pow_add_r by (pose proof (Pos2Z.is_pos p); omega).
    f_equal. omega.
  Qed.

  Lemma Z_shiftr_ones' : forall a n, 0 <= a < 2 ^ n -> forall i, (0 <= i) ->
    Z.shiftr a i <= Z.ones (n - i) \/ n <= i.
  Proof.
    intros until 1.
    apply natlike_ind.
    + unfold Z.ones.
      rewrite Z.shiftr_0_r, Z.shiftl_1_l, Z.sub_0_r.
      omega.
    + intros.
      destruct (Z_lt_le_dec x n); try omega.
      intuition.
      left.
      rewrite shiftr_succ.
      replace (n - Z.succ x) with (Z.pred (n - x)) by omega.
      rewrite Z_ones_pred by omega.
      apply Z_shiftr_1_r_le.
      assumption.
  Qed.

  Lemma Z_shiftr_ones : forall a n i, 0 <= a < 2 ^ n -> (0 <= i) -> (i <= n) ->
    Z.shiftr a i <= Z.ones (n - i) .
  Proof.
    intros a n i G G0 G1.
    destruct (Z_le_lt_eq_dec i n G1).
    + destruct (Z_shiftr_ones' a n G i G0); omega.
    + subst; rewrite Z.sub_diag.
      destruct (Z_eq_dec a 0).
      - subst; rewrite Z.shiftr_0_l; reflexivity.
      - rewrite Z.shiftr_eq_0; try omega; try reflexivity.
        apply Z.log2_lt_pow2; omega.
  Qed.

  Lemma Z_shiftr_upper_bound : forall a n, 0 <= n -> 0 <= a <= 2 ^ n -> Z.shiftr a n <= 1.
  Proof.
    intros a ? ? [a_nonneg a_upper_bound].
    apply Z_le_lt_eq_dec in a_upper_bound.
    destruct a_upper_bound.
    + destruct (Z_eq_dec 0 a).
      - subst; rewrite Z.shiftr_0_l; omega.
      - rewrite Z.shiftr_eq_0; auto; try omega.
        apply Z.log2_lt_pow2; auto; omega.
    + subst.
      rewrite Z.shiftr_div_pow2 by assumption.
      rewrite Z.div_same; try omega.
      assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; omega).
      omega.
  Qed.

(* prove that combinations of known positive/nonnegative numbers are positive/nonnegative *)
Ltac zero_bounds' :=
  repeat match goal with
  | [ |- 0 <= _ + _] => apply Z.add_nonneg_nonneg
  | [ |- 0 <= _ - _] => apply Z.le_0_sub
  | [ |- 0 <= _ * _] => apply Z.mul_nonneg_nonneg
  | [ |- 0 <= _ / _] => apply Z.div_pos
  | [ |- 0 <= _ ^ _ ] => apply Z.pow_nonneg
  | [ |- 0 <= Z.shiftr _ _] => apply Z.shiftr_nonneg
  | [ |- 0 < _ + _] => try solve [apply Z.add_pos_nonneg; zero_bounds'];
                       try solve [apply Z.add_nonneg_pos; zero_bounds']
  | [ |- 0 < _ - _] => apply Z.lt_0_sub
  | [ |- 0 < _ * _] => apply Z.lt_0_mul; left; split
  | [ |- 0 < _ / _] => apply Z.div_str_pos
  | [ |- 0 < _ ^ _ ] => apply Z.pow_pos_nonneg
  end; try omega; try prime_bound; auto.

Ltac zero_bounds := try omega; try prime_bound; zero_bounds'.

Lemma Z_ones_nonneg : forall i, (0 <= i) -> 0 <= Z.ones i.
Proof.
  apply natlike_ind.
  + unfold Z.ones. simpl; omega.
  + intros.
    rewrite Z_ones_succ by assumption.
    zero_bounds.
Qed.

Lemma Z_ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
Proof.
  intros.
  unfold Z.ones.
  rewrite Z.shiftl_1_l.
  apply Z.lt_succ_lt_pred.
  apply Z.pow_gt_1; omega.
Qed.

Lemma N_le_1_l : forall p, (1 <= N.pos p)%N.
Proof.
  destruct p; cbv; congruence.
Qed.

Lemma Pos_land_upper_bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
Proof.
  induction a; destruct b; intros; try solve [cbv; congruence];
    simpl; specialize (IHa b); case_eq (Pos.land a b); intro; simpl;
    try (apply N_le_1_l || apply N.le_0_l); intro land_eq;
    rewrite land_eq in *; unfold N.le, N.compare in *;
    rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
    try assumption.
  destruct (p ?=a)%positive; cbv; congruence.
Qed.

Lemma Z_land_upper_bound_l : forall a b, (0 <= a) -> (0 <= b) ->
  Z.land a b <= a.
Proof.
  intros.
  destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
  cbv [Z.land].
  rewrite <-N2Z.inj_pos, <-N2Z.inj_le.
  auto using Pos_land_upper_bound_l.
Qed.

Lemma Z_land_upper_bound_r : forall a b, (0 <= a) -> (0 <= b) ->
  Z.land a b <= b.
Proof.
  intros.
  rewrite Z.land_comm.
  auto using Z_land_upper_bound_l.
Qed.

Lemma Z_le_fold_right_max : forall low l x, (forall y, In y l -> low <= y) ->
  In x l -> x <= fold_right Z.max low l.
Proof.
  induction l; intros ? lower_bound In_list; [cbv [In] in *; intuition | ].
  simpl.
  destruct (in_inv In_list); subst.
  + apply Z.le_max_l.
  + etransitivity.
    - apply IHl; auto; intuition.
    - apply Z.le_max_r.
Qed.

Lemma Z_le_fold_right_max_initial : forall low l, low <= fold_right Z.max low l.
Proof.
  induction l; intros; try reflexivity.
  etransitivity; [ apply IHl | apply Z.le_max_r ].
Qed.

  (* TODO : move to ZUtil *)
  Lemma Z_lor_shiftl : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor a (Z.shiftl b n) = a + (Z.shiftl b n).
  Proof.
    intros.
    apply Z.bits_inj'; intros t ?.
    rewrite Z.lor_spec, Z.shiftl_spec by assumption.
    destruct (Z_lt_dec t n).
    + rewrite Z_testbit_add_shiftl_low by omega.
      rewrite Z.testbit_neg_r with (n := t - n) by omega.
      apply Bool.orb_false_r.
    + rewrite Z_testbit_add_shiftl_high by omega.
      replace (Z.testbit a t) with false; [ apply Bool.orb_false_l | ].
      symmetry.
      apply Z.testbit_false; try omega.
      rewrite Z.div_small; try reflexivity.
      split; try eapply Z.lt_le_trans with (m := 2 ^ n); try omega.
      apply Z.pow_le_mono_r; omega.
  Qed.
