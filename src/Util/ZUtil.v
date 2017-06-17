Require Import Coq.ZArith.Zpower Coq.ZArith.Znumtheory Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Coq.Structures.Equalities.
Require Import Coq.omega.Omega Coq.micromega.Psatz Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.Contains.
Require Import Crypto.Util.Tactics.Not.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Notations.
Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.ZUtil.Definitions.
Require Export Crypto.Util.ZUtil.Div.
Require Export Crypto.Util.ZUtil.EquivModulo.
Require Export Crypto.Util.ZUtil.Hints.
Require Export Crypto.Util.ZUtil.Land.
Require Export Crypto.Util.ZUtil.Modulo.
Require Export Crypto.Util.ZUtil.Modulo.PullPush.
Require Export Crypto.Util.ZUtil.Morphisms.
Require Export Crypto.Util.ZUtil.Notations.
Require Export Crypto.Util.ZUtil.Pow2Mod.
Require Export Crypto.Util.ZUtil.Quot.
Require Export Crypto.Util.ZUtil.Sgn.
Require Export Crypto.Util.ZUtil.Tactics.
Require Export Crypto.Util.ZUtil.Testbit.
Require Export Crypto.Util.ZUtil.ZSimplify.
Import Nat.
Local Open Scope Z.

Module Z.
  Lemma div_lt_upper_bound' a b q : 0 < b -> a < q * b -> a / b < q.
  Proof. intros; apply Z.div_lt_upper_bound; nia. Qed.
  Hint Resolve div_lt_upper_bound' : zarith.

  Lemma mul_comm3 x y z : x * (y * z) = y * (x * z).
  Proof. lia. Qed.

  Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
  Proof. intros; omega. Qed.
  Hint Resolve positive_is_nonzero : zarith.

  Lemma div_positive_gt_0 : forall a b, a > 0 -> b > 0 -> a mod b = 0 ->
    a / b > 0.
  Proof.
    intros; rewrite Z.gt_lt_iff.
    apply Z.div_str_pos.
    split; intuition auto with omega.
    apply Z.divide_pos_le; try (apply Zmod_divide); omega.
  Qed.

  Lemma pos_pow_nat_pos : forall x n,
    Z.pos x ^ Z.of_nat n > 0.
  Proof.
    do 2 (try intros x n; induction n as [|n]; subst; simpl in *; auto with zarith).
    rewrite <- Pos.add_1_r, Zpower_pos_is_exp.
    apply Zmult_gt_0_compat; auto; reflexivity.
  Qed.

  (** TODO: Should we get rid of this duplicate? *)
  Notation gt0_neq0 := positive_is_nonzero (only parsing).

  Lemma pow_Z2N_Zpow : forall a n, 0 <= a ->
    ((Z.to_nat a) ^ n = Z.to_nat (a ^ Z.of_nat n)%Z)%nat.
  Proof.
    intros a n H; induction n as [|n IHn]; try reflexivity.
    rewrite Nat2Z.inj_succ.
    rewrite pow_succ_r by apply le_0_n.
    rewrite Z.pow_succ_r by apply Zle_0_nat.
    rewrite IHn.
    rewrite Z2Nat.inj_mul; auto using Z.pow_nonneg.
  Qed.

  Lemma pow_Zpow : forall a n : nat, Z.of_nat (a ^ n) = Z.of_nat a ^ Z.of_nat n.
  Proof with auto using Zle_0_nat, Z.pow_nonneg.
    intros; apply Z2Nat.inj...
    rewrite <- pow_Z2N_Zpow, !Nat2Z.id...
  Qed.
  Hint Rewrite pow_Zpow : push_Zof_nat.
  Hint Rewrite <- pow_Zpow : pull_Zof_nat.

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
      Z.divide_exists_mul; [ | pose proof (Z.mod_pos_bound n 2); omega].
      rewrite divide2_n.
      apply Z.even_mul.
    } {
      intro n_even.
      pose proof (Zmod_even n) as H.
      rewrite n_even in H.
      apply Zmod_divide; omega || auto.
    }
  Qed.

  Lemma prime_odd_or_2 : forall p (prime_p : prime p), p = 2 \/ Z.odd p = true.
  Proof.
    intros p prime_p.
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
    destruct c_id; [omega | destruct H; [omega | destruct H; auto] ].
    pose proof (prime_ge_2 p prime_p); omega.
  Qed.

  Lemma shiftr_add_shiftl_high : forall n m a b, 0 <= n <= m -> 0 <= a < 2 ^ n ->
    Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr b (m - n).
  Proof.
    intros n m a b H H0.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by omega.
    replace (2 ^ m) with (2 ^ n * 2 ^ (m - n)) by
      (rewrite <-Z.pow_add_r by omega; f_equal; ring).
    rewrite <-Z.div_div, Z.div_add, (Z.div_small a) ; try solve
      [assumption || apply Z.pow_nonzero || apply Z.pow_pos_nonneg; omega].
    f_equal; ring.
  Qed.
  Hint Rewrite Z.shiftr_add_shiftl_high using zutil_arith : pull_Zshift.
  Hint Rewrite <- Z.shiftr_add_shiftl_high using zutil_arith : push_Zshift.

  Lemma shiftr_add_shiftl_low : forall n m a b, 0 <= m <= n -> 0 <= a < 2 ^ n ->
    Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr a m + Z.shiftr b (m - n).
  Proof.
    intros n m a b H H0.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2, Z.shiftr_mul_pow2 by omega.
    replace (2 ^ n) with (2 ^ (n - m) * 2 ^ m) by
      (rewrite <-Z.pow_add_r by omega; f_equal; ring).
    rewrite Z.mul_assoc, Z.div_add by (apply Z.pow_nonzero; omega).
    repeat f_equal; ring.
  Qed.
  Hint Rewrite Z.shiftr_add_shiftl_low using zutil_arith : pull_Zshift.
  Hint Rewrite <- Z.shiftr_add_shiftl_low using zutil_arith : push_Zshift.

  Lemma testbit_add_shiftl_high : forall i, (0 <= i) -> forall a b n, (0 <= n <= i) ->
    0 <= a < 2 ^ n ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit b (i - n).
  Proof.
    intros i ?.
    apply natlike_ind with (x := i); [ intros a b n | intros x H0 H1 a b n | ]; intros; try assumption;
      (destruct (Z_eq_dec 0 n); [ subst; rewrite Z.pow_0_r in *;
       replace a with 0 by omega; f_equal; ring | ]); try omega.
    rewrite <-Z.add_1_r at 1. rewrite <-Z.shiftr_spec by assumption.
    replace (Z.succ x - n) with (x - (n - 1)) by ring.
    rewrite shiftr_add_shiftl_low, <-Z.shiftl_opp_r with (a := b) by omega.
    rewrite <-H1 with (a := Z.shiftr a 1); try omega; [ repeat f_equal; ring | ].
    rewrite Z.shiftr_div_pow2 by omega.
    split; apply Z.div_pos || apply Z.div_lt_upper_bound;
      try solve [rewrite ?Z.pow_1_r; omega].
    rewrite <-Z.pow_add_r by omega.
    replace (1 + (n - 1)) with n by ring; omega.
  Qed.
  Hint Rewrite testbit_add_shiftl_high using zutil_arith : Ztestbit.

  Lemma nonneg_pow_pos a b : 0 < a -> 0 < a^b -> 0 <= b.
  Proof.
    destruct (Z_lt_le_dec b 0); intros; auto.
    erewrite Z.pow_neg_r in * by eassumption.
    omega.
  Qed.
  Hint Resolve nonneg_pow_pos (fun n => nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
  Lemma nonneg_pow_pos_helper a b dummy : 0 < a -> 0 <= dummy < a^b -> 0 <= b.
  Proof. eauto with zarith omega. Qed.
  Hint Resolve nonneg_pow_pos_helper (fun n dummy => nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.

  Lemma testbit_add_shiftl_full i (Hi : 0 <= i) a b n (Ha : 0 <= a < 2^n)
    : Z.testbit (a + b << n) i
      = if (i <? n) then Z.testbit a i else Z.testbit b (i - n).
  Proof.
    assert (0 < 2^n) by omega.
    assert (0 <= n) by eauto 2 with zarith.
    pose proof (Zlt_cases i n); break_match; autorewrite with Ztestbit; reflexivity.
  Qed.
  Hint Rewrite testbit_add_shiftl_full using zutil_arith : Ztestbit.

  Lemma land_add_land : forall n m a b, (m <= n)%nat ->
    Z.land ((Z.land a (Z.ones (Z.of_nat n))) + (Z.shiftl b (Z.of_nat n))) (Z.ones (Z.of_nat m)) = Z.land a (Z.ones (Z.of_nat m)).
  Proof.
    intros n m a b H.
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
  Hint Rewrite Z.shiftr_succ using zutil_arith : push_Zshift.
  Hint Rewrite <- Z.shiftr_succ using zutil_arith : pull_Zshift.

  Lemma pow2_lt_or_divides : forall a b, 0 <= b ->
    2 ^ a < 2 ^ b \/ (2 ^ a) mod 2 ^ b = 0.
  Proof.
    intros a b H.
    destruct (Z_lt_dec a b); [left|right].
    { apply Z.pow_lt_mono_r; auto; omega. }
    { replace a with (a - b + b) by ring.
      rewrite Z.pow_add_r by omega.
      apply Z.mod_mul, Z.pow_nonzero; omega. }
  Qed.

  Lemma odd_mod : forall a b, (b <> 0)%Z ->
    Z.odd (a mod b) = if Z.odd b then xorb (Z.odd a) (Z.odd (a / b)) else Z.odd a.
  Proof.
    intros a b H.
    rewrite Zmod_eq_full by assumption.
    rewrite <-Z.add_opp_r, Z.odd_add, Z.odd_opp, Z.odd_mul.
    case_eq (Z.odd b); intros; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; auto using Bool.xorb_false_r.
  Qed.

  Lemma mod_same_pow : forall a b c, 0 <= c <= b -> a ^ b mod a ^ c = 0.
  Proof.
    intros a b c H.
    replace b with (b - c + c) by ring.
    rewrite Z.pow_add_r by omega.
    apply Z_mod_mult.
  Qed.
  Hint Rewrite mod_same_pow using zutil_arith : zsimplify.

  Lemma ones_succ : forall x, (0 <= x) ->
    Z.ones (Z.succ x) = 2 ^ x + Z.ones x.
  Proof.
    unfold Z.ones; intros.
    rewrite !Z.shiftl_1_l.
    rewrite Z.add_pred_r.
    apply Z.succ_inj.
    rewrite !Z.succ_pred.
    rewrite Z.pow_succ_r; omega.
  Qed.

  Lemma div_floor : forall a b c, 0 < b -> a < b * (Z.succ c) -> a / b <= c.
  Proof.
    intros.
    apply Z.lt_succ_r.
    apply Z.div_lt_upper_bound; try omega.
  Qed.

  Lemma shiftr_1_r_le : forall a b, a <= b ->
    Z.shiftr a 1 <= Z.shiftr b 1.
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.pow_1_r by omega.
    apply Z.div_le_mono; omega.
  Qed.
  Hint Resolve shiftr_1_r_le : zarith.

  Lemma shiftr_le : forall a b i : Z, 0 <= i -> a <= b -> a >> i <= b >> i.
  Proof.
    intros a b i ?; revert a b. apply natlike_ind with (x := i); intros; auto.
    rewrite !shiftr_succ, shiftr_1_r_le; eauto. reflexivity.
  Qed.
  Hint Resolve shiftr_le : zarith.

  Lemma ones_pred : forall i, 0 < i -> Z.ones (Z.pred i) = Z.shiftr (Z.ones i) 1.
  Proof.
    induction i as [|p|p]; [ | | pose proof (Pos2Z.neg_is_neg p) ]; try omega.
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
  Hint Rewrite <- ones_pred using zutil_arith : push_Zshift.

  Lemma shiftr_ones' : forall a n, 0 <= a < 2 ^ n -> forall i, (0 <= i) ->
    Z.shiftr a i <= Z.ones (n - i) \/ n <= i.
  Proof.
    intros a n H.
    apply natlike_ind.
    + unfold Z.ones.
      rewrite Z.shiftr_0_r, Z.shiftl_1_l, Z.sub_0_r.
      omega.
    + intros x H0 H1.
      destruct (Z_lt_le_dec x n); try omega.
      intuition auto with zarith lia.
      left.
      rewrite shiftr_succ.
      replace (n - Z.succ x) with (Z.pred (n - x)) by omega.
      rewrite Z.ones_pred by omega.
      apply Z.shiftr_1_r_le.
      assumption.
  Qed.

  Lemma shiftr_ones : forall a n i, 0 <= a < 2 ^ n -> (0 <= i) -> (i <= n) ->
    Z.shiftr a i <= Z.ones (n - i) .
  Proof.
    intros a n i G G0 G1.
    destruct (Z_le_lt_eq_dec i n G1).
    + destruct (Z.shiftr_ones' a n G i G0); omega.
    + subst; rewrite Z.sub_diag.
      destruct (Z_eq_dec a 0).
      - subst; rewrite Z.shiftr_0_l; reflexivity.
      - rewrite Z.shiftr_eq_0; try omega; try reflexivity.
        apply Z.log2_lt_pow2; omega.
  Qed.
  Hint Resolve shiftr_ones : zarith.

  Lemma shiftr_upper_bound : forall a n, 0 <= n -> 0 <= a <= 2 ^ n -> Z.shiftr a n <= 1.
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
  Hint Resolve shiftr_upper_bound : zarith.

  Lemma lor_shiftl : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor a (Z.shiftl b n) = a + (Z.shiftl b n).
  Proof.
    intros a b n H H0.
    apply Z.bits_inj'; intros t ?.
    rewrite Z.lor_spec, Z.shiftl_spec by assumption.
    destruct (Z_lt_dec t n).
    + rewrite Z.testbit_add_shiftl_low by omega.
      rewrite Z.testbit_neg_r with (n := t - n) by omega.
      apply Bool.orb_false_r.
    + rewrite testbit_add_shiftl_high by omega.
      replace (Z.testbit a t) with false; [ apply Bool.orb_false_l | ].
      symmetry.
      apply Z.testbit_false; try omega.
      rewrite Z.div_small; try reflexivity.
      split; try eapply Z.lt_le_trans with (m := 2 ^ n); try omega.
      apply Z.pow_le_mono_r; omega.
  Qed.
  Hint Rewrite <- Z.lor_shiftl using zutil_arith : convert_to_Ztestbit.

  Lemma lor_shiftl' : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor (Z.shiftl b n) a = (Z.shiftl b n) + a.
  Proof.
    intros; rewrite Z.lor_comm, Z.add_comm; apply lor_shiftl; assumption.
  Qed.
  Hint Rewrite <- Z.lor_shiftl' using zutil_arith : convert_to_Ztestbit.

  Lemma shiftl_spec_full a n m
    : Z.testbit (a << n) m = if Z_lt_dec m n
                             then false
                             else if Z_le_dec 0 m
                                  then Z.testbit a (m - n)
                                  else false.
  Proof.
    repeat break_match; auto using Z.shiftl_spec_low, Z.shiftl_spec, Z.testbit_neg_r with omega.
  Qed.
  Hint Rewrite shiftl_spec_full : Ztestbit_full.

  Lemma shiftr_spec_full a n m
    : Z.testbit (a >> n) m = if Z_lt_dec m (-n)
                             then false
                             else if Z_le_dec 0 m
                                  then Z.testbit a (m + n)
                                  else false.
  Proof.
    rewrite <- Z.shiftl_opp_r, shiftl_spec_full, Z.sub_opp_r; reflexivity.
  Qed.
  Hint Rewrite shiftr_spec_full : Ztestbit_full.

  Lemma lnot_sub1 x : Z.lnot (x-1) = (-x).
  Proof.
    replace (-x) with (- (1) - (x - 1)) by omega.
    rewrite <-(Z.add_lnot_diag (x-1)); omega.
  Qed.

  Lemma lnot_opp x : Z.lnot (- x) = x-1.
  Proof.
    rewrite <-Z.lnot_involutive, lnot_sub1; reflexivity.
  Qed.

  Lemma testbit_sub_pow2 n i x (i_range:0 <= i < n) (x_range:0 < x < 2 ^ n) :
    Z.testbit (2 ^ n - x) i = negb (Z.testbit (x - 1)  i).
  Proof.
    rewrite <-Z.lnot_spec, lnot_sub1 by omega.
    rewrite <-(Z.mod_pow2_bits_low (-x) _ _ (proj2 i_range)).
    f_equal.
    rewrite Z.mod_opp_l_nz; autorewrite with zsimplify; omega.
  Qed.

  Lemma ones_nonneg : forall i, (0 <= i) -> 0 <= Z.ones i.
  Proof.
    apply natlike_ind.
    + unfold Z.ones. simpl; omega.
    + intros.
      rewrite Z.ones_succ by assumption.
      Z.zero_bounds.
  Qed.
  Hint Resolve ones_nonneg : zarith.

  Lemma ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
  Proof.
    intros.
    unfold Z.ones.
    rewrite Z.shiftl_1_l.
    apply Z.lt_succ_lt_pred.
    apply Z.pow_gt_1; omega.
  Qed.
  Hint Resolve ones_pos_pos : zarith.

  Lemma pow2_mod_id_iff : forall a n, 0 <= n ->
                                      (Z.pow2_mod a n = a <-> 0 <= a < 2 ^ n).
  Proof.
    intros a n H.
    rewrite Z.pow2_mod_spec by assumption.
    assert (0 < 2 ^ n) by Z.zero_bounds.
    rewrite Z.mod_small_iff by omega.
    split; intros; intuition omega.
  Qed.

  Lemma testbit_false_bound : forall a x, 0 <= x ->
    (forall n, ~ (n < x) -> Z.testbit a n = false) ->
    a < 2 ^ x.
  Proof.
    intros a x H H0.
    assert (H1 : a = Z.pow2_mod a x). {
     apply Z.bits_inj'; intros.
     rewrite Z.testbit_pow2_mod by omega; break_match; auto.
    }
    rewrite H1.
    rewrite Z.pow2_mod_spec; try apply Z.mod_pos_bound; Z.zero_bounds.
  Qed.

  Lemma lor_range : forall x y n, 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n ->
                                  0 <= Z.lor x y < 2 ^ n.
  Proof.
    intros x y n H H0; assert (0 <= n) by auto with zarith omega.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => rewrite Z.lor_spec
           | |- _ => rewrite Z.testbit_eqb by auto with zarith omega
           | |- _ => rewrite !Z.div_small by (split; try omega; eapply Z.lt_le_trans;
                             [ intuition eassumption | apply Z.pow_le_mono_r; omega])
           | |- _ => split
           | |- _ => apply testbit_false_bound
           | |- _ => solve [auto with zarith]
           | |- _ => solve [apply Z.lor_nonneg; intuition auto]
           end.
  Qed.
  Hint Resolve lor_range : zarith.

  Lemma lor_shiftl_bounds : forall x y n m,
      (0 <= n)%Z -> (0 <= m)%Z ->
      (0 <= x < 2 ^ m)%Z ->
      (0 <= y < 2 ^ n)%Z ->
      (0 <= Z.lor y (Z.shiftl x n) < 2 ^ (n + m))%Z.
  Proof.
    intros x y n m H H0 H1 H2.
    apply Z.lor_range.
    { split; try omega.
      apply Z.lt_le_trans with (m := (2 ^ n)%Z); try omega.
      apply Z.pow_le_mono_r; omega. }
    { rewrite Z.shiftl_mul_pow2 by omega.
      rewrite Z.pow_add_r by omega.
      split; Z.zero_bounds.
      rewrite Z.mul_comm.
      apply Z.mul_lt_mono_pos_l; omega. }
  Qed.

  Lemma N_le_1_l : forall p, (1 <= N.pos p)%N.
  Proof.
    destruct p; cbv; congruence.
  Qed.

  Lemma Pos_land_upper_bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
  Proof.
    induction a as [a IHa|a IHa|]; destruct b as [b|b|]; try solve [cbv; congruence];
      simpl; specialize (IHa b); case_eq (Pos.land a b); intro p; simpl;
      try (apply N_le_1_l || apply N.le_0_l); intro land_eq;
      rewrite land_eq in *; unfold N.le, N.compare in *;
      rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
      try assumption.
    destruct (p ?=a)%positive; cbv; congruence.
  Qed.

  Lemma land_upper_bound_l : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= a.
  Proof.
    intros a b H H0.
    destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
    cbv [Z.land].
    rewrite <-N2Z.inj_pos, <-N2Z.inj_le.
    auto using Pos_land_upper_bound_l.
  Qed.

  Lemma land_upper_bound_r : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= b.
  Proof.
    intros.
    rewrite Z.land_comm.
    auto using Z.land_upper_bound_l.
  Qed.

  Lemma le_fold_right_max : forall low l x, (forall y, In y l -> low <= y) ->
    In x l -> x <= fold_right Z.max low l.
  Proof.
    induction l as [|a l IHl]; intros ? lower_bound In_list; [cbv [In] in *; intuition | ].
    simpl.
    destruct (in_inv In_list); subst.
    + apply Z.le_max_l.
    + etransitivity.
      - apply IHl; auto; intuition auto with datatypes.
      - apply Z.le_max_r.
  Qed.

  Lemma le_fold_right_max_initial : forall low l, low <= fold_right Z.max low l.
  Proof.
    induction l as [|a l IHl]; intros; try reflexivity.
    etransitivity; [ apply IHl | apply Z.le_max_r ].
  Qed.

  Lemma add_compare_mono_r: forall n m p, (n + p ?= m + p) = (n ?= m).
  Proof.
    intros n m p.
    rewrite <-!(Z.add_comm p).
    apply Z.add_compare_mono_l.
  Qed.

  Lemma compare_add_shiftl : forall x1 y1 x2 y2 n, 0 <= n ->
    Z.pow2_mod x1 n = x1 -> Z.pow2_mod x2 n = x2  ->
    x1 + (y1 << n) ?= x2 + (y2 << n) =
      if Z_eq_dec y1 y2
      then x1 ?= x2
      else y1 ?= y2.
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress subst y1
           | |- _ => rewrite Z.shiftl_mul_pow2 by omega
           | |- _ => rewrite add_compare_mono_r
           | |- _ => rewrite <-Z.mul_sub_distr_r
           | |- _ => break_innermost_match_step
           | H : Z.pow2_mod _ _ = _ |- _ => rewrite pow2_mod_id_iff in H by omega
           | H : ?a <> ?b |- _ = (?a ?= ?b) =>
             case_eq (a ?= b); rewrite ?Z.compare_eq_iff, ?Z.compare_gt_iff, ?Z.compare_lt_iff
           | |- _ + (_ * _) > _ + (_ * _) => cbv [Z.gt]
           | |- _ + (_ * ?x) < _ + (_ * ?x) =>
             apply Z.lt_sub_lt_add; apply Z.lt_le_trans with (m := 1 * x); [omega|]
           | |- _ => apply Z.mul_le_mono_nonneg_r; omega
           | |- _ => reflexivity
           | |- _ => congruence
           end.
  Qed.

  Lemma ones_le x y : x <= y -> Z.ones x <= Z.ones y.
  Proof.
    rewrite !Z.ones_equiv; auto with zarith.
  Qed.
  Hint Resolve ones_le : zarith.

  Lemma mul_div_le x y z
        (Hx : 0 <= x) (Hy : 0 <= y) (Hz : 0 < z)
        (Hyz : y <= z)
    : x * y / z <= x.
  Proof.
    transitivity (x * z / z); [ | rewrite Z.div_mul by lia; lia ].
    apply Z_div_le; nia.
  Qed.

  Hint Resolve mul_div_le : zarith.

  Lemma div_mul_diff_exact a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * a / b = c * (a / b) + (c * (a mod b)) / b.
  Proof.
    rewrite (Z_div_mod_eq a b) at 1 by lia.
    rewrite Z.mul_add_distr_l.
    replace (c * (b * (a / b))) with ((c * (a / b)) * b) by lia.
    rewrite Z.div_add_l by lia.
    lia.
  Qed.

  Lemma div_mul_diff_exact' a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * (a / b) = c * a / b - (c * (a mod b)) / b.
  Proof.
    rewrite div_mul_diff_exact by assumption; lia.
  Qed.

  Lemma div_mul_diff_exact'' a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : a * c / b = (a / b) * c + (c * (a mod b)) / b.
  Proof.
    rewrite (Z.mul_comm a c), div_mul_diff_exact by lia; lia.
  Qed.

  Lemma div_mul_diff_exact''' a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : (a / b) * c = a * c / b - (c * (a mod b)) / b.
  Proof.
    rewrite (Z.mul_comm a c), div_mul_diff_exact by lia; lia.
  Qed.

  Lemma div_mul_diff a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * a / b - c * (a / b) <= c.
  Proof.
    rewrite div_mul_diff_exact by assumption.
    ring_simplify; auto with zarith.
  Qed.

  Lemma div_mul_le_le a b c
    :  0 <= a -> 0 < b -> 0 <= c -> c * (a / b) <= c * a / b <= c * (a / b) + c.
  Proof.
    pose proof (Z.div_mul_diff a b c); split; try apply Z.div_mul_le; lia.
  Qed.

  Lemma div_mul_le_le_offset a b c
    : 0 <= a -> 0 < b -> 0 <= c -> c * a / b - c <= c * (a / b).
  Proof.
    pose proof (Z.div_mul_le_le a b c); lia.
  Qed.

  Hint Resolve Zmult_le_compat_r Zmult_le_compat_l Z_div_le Z.div_mul_le_le_offset Z.add_le_mono Z.sub_le_mono : zarith.

  Lemma log2_nonneg' n a : n <= 0 -> n <= Z.log2 a.
  Proof.
    intros; transitivity 0; auto with zarith.
  Qed.

  Hint Resolve log2_nonneg' : zarith.

  Lemma le_lt_to_log2 x y z : 0 <= z -> 0 < y -> 2^x <= y < 2^z -> x <= Z.log2 y < z.
  Proof.
    destruct (Z_le_gt_dec 0 x); auto with concl_log2 lia.
  Qed.

  Lemma div_x_y_x x y : 0 < x -> 0 < y -> x / y / x = 1 / y.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm y x), <- Z.div_div, Z.div_same by lia.
    reflexivity.
  Qed.

  Hint Rewrite div_x_y_x using zutil_arith : zsimplify.

  Lemma mod_opp_l_z_iff a b (H : b <> 0) : a mod b = 0 <-> (-a) mod b = 0.
  Proof.
    split; intro H'; apply Z.mod_opp_l_z in H'; rewrite ?Z.opp_involutive in H'; assumption.
  Qed.

  Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
  Proof. omega. Qed.

  Hint Rewrite <- mod_opp_l_z_iff using zutil_arith : zsimplify.
  Hint Rewrite opp_eq_0_iff : zsimplify.

  Lemma sub_pos_bound a b X : 0 <= a < X -> 0 <= b < X -> -X < a - b < X.
  Proof. lia. Qed.

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

  Lemma shiftl_opp_l a n
    : Z.shiftl (-a) n = - Z.shiftl a n - (if Z_zerop (a mod 2 ^ (- n)) then 0 else 1).
  Proof.
    destruct (Z_dec 0 n) as [ [?|?] | ? ];
      subst;
      rewrite ?Z.pow_neg_r by omega;
      autorewrite with zsimplify_const;
      [ | | simpl; omega ].
    { rewrite !Z.shiftl_mul_pow2 by omega.
      nia. }
    { rewrite !Z.shiftl_div_pow2 by omega.
      rewrite Z.div_opp_l_complete by auto with zarith.
      reflexivity. }
  Qed.
  Hint Rewrite shiftl_opp_l : push_Zshift.
  Hint Rewrite <- shiftl_opp_l : pull_Zshift.

  Lemma shiftr_opp_l a n
    : Z.shiftr (-a) n = - Z.shiftr a n - (if Z_zerop (a mod 2 ^ n) then 0 else 1).
  Proof.
    unfold Z.shiftr; rewrite shiftl_opp_l at 1; rewrite Z.opp_involutive.
    reflexivity.
  Qed.
  Hint Rewrite shiftr_opp_l : push_Zshift.
  Hint Rewrite <- shiftr_opp_l : pull_Zshift.

  Lemma div_opp a : a <> 0 -> -a / a = -1.
  Proof.
    intros; autorewrite with pull_Zopp zsimplify; lia.
  Qed.

  Hint Rewrite Z.div_opp using zutil_arith : zsimplify.

  Lemma div_sub_1_0 x : x > 0 -> (x - 1) / x = 0.
  Proof. auto with zarith lia. Qed.

  Hint Rewrite div_sub_1_0 using zutil_arith : zsimplify.

  Lemma sub_pos_bound_div a b X : 0 <= a < X -> 0 <= b < X -> -1 <= (a - b) / X <= 0.
  Proof.
    intros H0 H1; pose proof (Z.sub_pos_bound a b X H0 H1).
    assert (Hn : -X <= a - b) by lia.
    assert (Hp : a - b <= X - 1) by lia.
    split; etransitivity; [ | apply Z_div_le, Hn; lia | apply Z_div_le, Hp; lia | ];
      instantiate; autorewrite with zsimplify; try reflexivity.
  Qed.

  Hint Resolve (fun a b X H0 H1 => proj1 (Z.sub_pos_bound_div a b X H0 H1))
       (fun a b X H0 H1 => proj1 (Z.sub_pos_bound_div a b X H0 H1)) : zarith.

  Lemma sub_pos_bound_div_eq a b X : 0 <= a < X -> 0 <= b < X -> (a - b) / X = if a <? b then -1 else 0.
  Proof.
    intros H0 H1; pose proof (Z.sub_pos_bound_div a b X H0 H1).
    destruct (a <? b) eqn:?; Z.ltb_to_lt.
    { cut ((a - b) / X <> 0); [ lia | ].
      autorewrite with zstrip_div; auto with zarith lia. }
    { autorewrite with zstrip_div; auto with zarith lia. }
  Qed.

  Lemma add_opp_pos_bound_div_eq a b X : 0 <= a < X -> 0 <= b < X -> (-b + a) / X = if a <? b then -1 else 0.
  Proof.
    rewrite !(Z.add_comm (-_)), !Z.add_opp_r.
    apply Z.sub_pos_bound_div_eq.
  Qed.

  Hint Rewrite Z.sub_pos_bound_div_eq Z.add_opp_pos_bound_div_eq using zutil_arith : zstrip_div.

  Lemma div_small_sym a b : 0 <= a < b -> 0 = a / b.
  Proof. intros; symmetry; apply Z.div_small; assumption. Qed.

  Lemma mod_small_sym a b : 0 <= a < b -> a = a mod b.
  Proof. intros; symmetry; apply Z.mod_small; assumption. Qed.

  Hint Resolve div_small_sym mod_small_sym : zarith.

  Lemma mod_eq_le_to_eq a b : 0 < a <= b -> a mod b = 0 -> a = b.
  Proof.
    intros H H'.
    assert (a = b * (a / b)) by auto with zarith lia.
    assert (a / b = 1) by nia.
    nia.
  Qed.
  Hint Resolve mod_eq_le_to_eq : zarith.

  Lemma div_same' a b : b <> 0 -> a = b -> a / b = 1.
  Proof.
    intros; subst; auto with zarith.
  Qed.
  Hint Resolve div_same' : zarith.

  Lemma mod_eq_le_div_1 a b : 0 < a <= b -> a mod b = 0 -> a / b = 1.
  Proof. auto with zarith. Qed.
  Hint Resolve mod_eq_le_div_1 : zarith.
  Hint Rewrite mod_eq_le_div_1 using zutil_arith : zsimplify.

  Lemma mod_neq_0_le_to_neq a b : a mod b <> 0 -> a <> b.
  Proof. repeat intro; subst; autorewrite with zsimplify in *; lia. Qed.
  Hint Resolve mod_neq_0_le_to_neq : zarith.

  Lemma div_small_neg x y : 0 < -x <= y -> x / y = -1.
  Proof.
    intro H; rewrite <- (Z.opp_involutive x).
    rewrite Z.div_opp_l_complete by lia.
    generalize dependent (-x); clear x; intros x H.
    pose proof (mod_neq_0_le_to_neq x y).
    autorewrite with zsimplify; edestruct Z_zerop; autorewrite with zsimplify in *; lia.
  Qed.
  Hint Rewrite div_small_neg using zutil_arith : zsimplify.

  Lemma div_sub_small x y z : 0 <= x < z -> 0 <= y <= z -> (x - y) / z = if x <? y then -1 else 0.
  Proof.
    pose proof (Zlt_cases x y).
    (destruct (x <? y) eqn:?);
      intros; autorewrite with zsimplify; try lia.
  Qed.
  Hint Rewrite div_sub_small using zutil_arith : zsimplify.

  Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
  Proof. lia. Qed.

  Lemma mul_div_lt_by_le x y z b : 0 <= y < z -> 0 <= x < b -> x * y / z < b.
  Proof.
    intros [? ?] [? ?]; eapply Z.le_lt_trans; [ | eassumption ].
    auto with zarith.
  Qed.
  Hint Resolve mul_div_lt_by_le : zarith.

  Definition pow_sub_r'
    := fun a b c y H0 H1 => @Logic.eq_trans _ _ _ y (@Z.pow_sub_r a b c H0 H1).
  Definition pow_sub_r'_sym
    := fun a b c y p H0 H1 => Logic.eq_sym (@Logic.eq_trans _ y _ _ (Logic.eq_sym p) (@Z.pow_sub_r a b c H0 H1)).
  Hint Resolve pow_sub_r' pow_sub_r'_sym Z.eq_le_incl : zarith.
  Hint Resolve (fun b => f_equal (fun e => b ^ e)) (fun e => f_equal (fun b => b ^ e)) : zarith.
  Definition mul_div_le'
    := fun x y z w p H0 H1 H2 H3 => @Z.le_trans _ _ w (@Z.mul_div_le x y z H0 H1 H2 H3) p.
  Hint Resolve mul_div_le' : zarith.
  Lemma mul_div_le'' x y z w : y <= w -> 0 <= x -> 0 <= y -> 0 < z -> x <= z -> x * y / z <= w.
  Proof.
    rewrite (Z.mul_comm x y); intros; apply mul_div_le'; assumption.
  Qed.
  Hint Resolve mul_div_le'' : zarith.

  Lemma two_p_two_eq_four : 2^(2) = 4.
  Proof. reflexivity. Qed.
  Hint Rewrite <- two_p_two_eq_four : push_Zpow.

  Lemma base_pow_neg b n : n < 0 -> b^n = 0.
  Proof.
    destruct n; intro H; try reflexivity; compute in H; congruence.
  Qed.
  Hint Rewrite base_pow_neg using zutil_arith : zsimplify.

  Lemma div_mod' a b : b <> 0 -> a = (a / b) * b + a mod b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod' using zutil_arith : zsimplify.

  Lemma div_mod'' a b : b <> 0 -> a = a mod b + b * (a / b).
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod'' using zutil_arith : zsimplify.

  Lemma div_mod''' a b : b <> 0 -> a = a mod b + (a / b) * b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod''' using zutil_arith : zsimplify.

  Lemma div_sub_mod_exact a b : b <> 0 -> a / b = (a - a mod b) / b.
  Proof.
    intro.
    rewrite (Z.div_mod a b) at 2 by lia.
    autorewrite with zsimplify.
    reflexivity.
  Qed.

  Definition opp_distr_if (b : bool) x y : -(if b then x else y) = if b then -x else -y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite opp_distr_if : push_Zopp.
  Hint Rewrite <- opp_distr_if : pull_Zopp.

  Lemma mul_r_distr_if (b : bool) x y z : z * (if b then x else y) = if b then z * x else z * y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mul_r_distr_if : push_Zmul.
  Hint Rewrite <- mul_r_distr_if : pull_Zmul.

  Lemma mul_l_distr_if (b : bool) x y z : (if b then x else y) * z = if b then x * z else y * z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mul_l_distr_if : push_Zmul.
  Hint Rewrite <- mul_l_distr_if : pull_Zmul.

  Lemma add_r_distr_if (b : bool) x y z : z + (if b then x else y) = if b then z + x else z + y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite add_r_distr_if : push_Zadd.
  Hint Rewrite <- add_r_distr_if : pull_Zadd.

  Lemma add_l_distr_if (b : bool) x y z : (if b then x else y) + z = if b then x + z else y + z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite add_l_distr_if : push_Zadd.
  Hint Rewrite <- add_l_distr_if : pull_Zadd.

  Lemma sub_r_distr_if (b : bool) x y z : z - (if b then x else y) = if b then z - x else z - y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite sub_r_distr_if : push_Zsub.
  Hint Rewrite <- sub_r_distr_if : pull_Zsub.

  Lemma sub_l_distr_if (b : bool) x y z : (if b then x else y) - z = if b then x - z else y - z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite sub_l_distr_if : push_Zsub.
  Hint Rewrite <- sub_l_distr_if : pull_Zsub.

  Lemma div_r_distr_if (b : bool) x y z : z / (if b then x else y) = if b then z / x else z / y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite div_r_distr_if : push_Zdiv.
  Hint Rewrite <- div_r_distr_if : pull_Zdiv.

  Lemma div_l_distr_if (b : bool) x y z : (if b then x else y) / z = if b then x / z else y / z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite div_l_distr_if : push_Zdiv.
  Hint Rewrite <- div_l_distr_if : pull_Zdiv.

  Lemma div_add_exact x y d : d <> 0 -> x mod d = 0 -> (x + y) / d = x / d + y / d.
  Proof.
    intros; rewrite (Z_div_exact_full_2 x d) at 1 by assumption.
    rewrite Z.div_add_l' by assumption; lia.
  Qed.
  Hint Rewrite div_add_exact using zutil_arith : zsimplify.

  Lemma sub_mod_mod_0 x d : (x - x mod d) mod d = 0.
  Proof.
    destruct (Z_zerop d); subst; autorewrite with push_Zmod zsimplify; reflexivity.
  Qed.
  Hint Resolve sub_mod_mod_0 : zarith.
  Hint Rewrite sub_mod_mod_0 : zsimplify.

  Lemma div_sub_mod_cond x y d
    : d <> 0
      -> (x - y) / d
         = x / d + ((x mod d - y) / d).
  Proof. clear.
         intro.
         replace (x - y) with ((x - x mod d) + (x mod d - y)) by lia.
         rewrite div_add_exact by auto with zarith.
         rewrite <- Z.div_sub_mod_exact by lia; lia.
  Qed.
  Hint Resolve div_sub_mod_cond : zarith.

  Lemma div_between n a b : 0 <= n -> b <> 0 -> n * b <= a < (1 + n) * b -> a / b = n.
  Proof. intros; Z.div_mod_to_quot_rem; nia. Qed.
  Hint Rewrite div_between using zutil_arith : zsimplify.

  Lemma mod_small_n n a b : 0 <= n -> b <> 0 -> n * b <= a < (1 + n) * b -> a mod b = a - n * b.
  Proof. intros; erewrite Zmod_eq_full, div_between by eassumption. reflexivity. Qed.
  Hint Rewrite mod_small_n using zutil_arith : zsimplify.

  Lemma div_between_1 a b : b <> 0 -> b <= a < 2 * b -> a / b = 1.
  Proof. intros; rewrite (div_between 1) by lia; reflexivity. Qed.
  Hint Rewrite div_between_1 using zutil_arith : zsimplify.

  Lemma mod_small_1 a b : b <> 0 -> b <= a < 2 * b -> a mod b = a - b.
  Proof. intros; rewrite (mod_small_n 1) by lia; lia. Qed.
  Hint Rewrite mod_small_1 using zutil_arith : zsimplify.

  Lemma div_between_if n a b : 0 <= n -> b <> 0 -> n * b <= a < (2 + n) * b -> (a / b = if (1 + n) * b <=? a then 1 + n else n)%Z.
  Proof.
    intros.
    break_match; Z.ltb_to_lt;
      apply div_between; lia.
  Qed.

  Lemma mod_small_n_if n a b : 0 <= n -> b <> 0 -> n * b <= a < (2 + n) * b -> a mod b = a - (if (1 + n) * b <=? a then (1 + n) else n) * b.
  Proof. intros; erewrite Zmod_eq_full, div_between_if by eassumption; autorewrite with zsimplify_const. reflexivity. Qed.

  Lemma div_between_0_if a b : b <> 0 -> 0 <= a < 2 * b -> a / b = if b <=? a then 1 else 0.
  Proof. intros; rewrite (div_between_if 0) by lia; autorewrite with zsimplify_const; reflexivity. Qed.

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
    omega.
  Qed.


  Lemma leb_add_same x y : (x <=? y + x) = (0 <=? y).
  Proof. destruct (x <=? y + x) eqn:?, (0 <=? y) eqn:?; Z.ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite leb_add_same : zsimplify.

  Lemma ltb_add_same x y : (x <? y + x) = (0 <? y).
  Proof. destruct (x <? y + x) eqn:?, (0 <? y) eqn:?; Z.ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite ltb_add_same : zsimplify.

  Lemma geb_add_same x y : (x >=? y + x) = (0 >=? y).
  Proof. destruct (x >=? y + x) eqn:?, (0 >=? y) eqn:?; Z.ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite geb_add_same : zsimplify.

  Lemma gtb_add_same x y : (x >? y + x) = (0 >? y).
  Proof. destruct (x >? y + x) eqn:?, (0 >? y) eqn:?; Z.ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite gtb_add_same : zsimplify.

  Lemma shiftl_add x y z : 0 <= z -> (x + y) << z = (x << z) + (y << z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftl_add using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftl_add using zutil_arith : pull_Zshift.

  Lemma shiftr_add x y z : z <= 0 -> (x + y) >> z = (x >> z) + (y >> z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftr_add using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftr_add using zutil_arith : pull_Zshift.

  Lemma shiftl_sub x y z : 0 <= z -> (x - y) << z = (x << z) - (y << z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftl_sub using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftl_sub using zutil_arith : pull_Zshift.

  Lemma shiftr_sub x y z : z <= 0 -> (x - y) >> z = (x >> z) - (y >> z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftr_sub using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftr_sub using zutil_arith : pull_Zshift.

  Lemma shl_shr_lt x y n m (Hx : 0 <= x < 2^n) (Hy : 0 <= y < 2^n) (Hm : 0 <= m <= n)
    : 0 <= (x >> (n - m)) + ((y << m) mod 2^n) < 2^n.
  Proof.
    cut (0 <= (x >> (n - m)) + ((y << m) mod 2^n) <= 2^n - 1); [ omega | ].
    assert (0 <= x <= 2^n - 1) by omega.
    assert (0 <= y <= 2^n - 1) by omega.
    assert (0 < 2 ^ (n - m)) by auto with zarith.
    assert (0 <= y mod 2 ^ (n - m) < 2^(n-m)) by auto with zarith.
    assert (0 <= y mod 2 ^ (n - m) <= 2 ^ (n - m) - 1) by omega.
    assert (0 <= (y mod 2 ^ (n - m)) * 2^m <= (2^(n-m) - 1)*2^m) by auto with zarith.
    assert (0 <= x / 2^(n-m) < 2^n / 2^(n-m)).
    { split; Z.zero_bounds.
      apply Z.div_lt_upper_bound; autorewrite with pull_Zpow zsimplify; nia. }
    autorewrite with Zshift_to_pow.
    split; Z.zero_bounds.
    replace (2^n) with (2^(n-m) * 2^m) by (autorewrite with pull_Zpow; f_equal; omega).
    rewrite Zmult_mod_distr_r.
    autorewrite with pull_Zpow zsimplify push_Zmul in * |- .
    nia.
  Qed.

  Lemma add_shift_mod x y n m
        (Hx : 0 <= x < 2^n) (Hy : 0 <= y)
        (Hn : 0 <= n) (Hm : 0 < m)
    : (x + y << n) mod (m * 2^n) = x + (y mod m) << n.
  Proof.
    pose proof (Z.mod_bound_pos y m).
    specialize_by omega.
    assert (0 < 2^n) by auto with zarith.
    autorewrite with Zshift_to_pow.
    rewrite Zplus_mod, !Zmult_mod_distr_r.
    rewrite Zplus_mod, !Zmod_mod, <- Zplus_mod.
    rewrite !(Zmod_eq (_ + _)) by nia.
    etransitivity; [ | apply Z.add_0_r ].
    rewrite <- !Z.add_opp_r, <- !Z.add_assoc.
    repeat apply f_equal.
    ring_simplify.
    cut (((x + y mod m * 2 ^ n) / (m * 2 ^ n)) = 0); [ nia | ].
    apply Z.div_small; split; nia.
  Qed.

  Lemma add_mul_mod x y n m
        (Hx : 0 <= x < 2^n) (Hy : 0 <= y)
        (Hn : 0 <= n) (Hm : 0 < m)
    : (x + y * 2^n) mod (m * 2^n) = x + (y mod m) * 2^n.
  Proof.
    generalize (add_shift_mod x y n m).
    autorewrite with Zshift_to_pow; auto.
  Qed.

  Lemma lt_pow_2_shiftr : forall a n, 0 <= a < 2 ^ n -> a >> n = 0.
  Proof.
    intros a n H.
    destruct (Z_le_dec 0 n).
    + rewrite Z.shiftr_div_pow2 by assumption.
      auto using Z.div_small.
    + assert (2 ^ n = 0) by (apply Z.pow_neg_r; omega).
      omega.
  Qed.

  Hint Rewrite Z.pow2_bits_eqb using zutil_arith : Ztestbit.
  Lemma pow_2_shiftr : forall n, 0 <= n -> (2 ^ n) >> n = 1.
  Proof.
    intros; apply Z.bits_inj'; intros.
    replace 1 with (2 ^ 0) by ring.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress rewrite ?Z.eqb_eq, ?Z.eqb_neq in *
           | |- _ => progress autorewrite with Ztestbit
           | |- context[Z.eqb ?a ?b] => case_eq (Z.eqb a b)
           | |- _ => reflexivity || omega
           end.
  Qed.

  Lemma lt_mul_2_pow_2_shiftr : forall a n, 0 <= a < 2 * 2 ^ n ->
                                            a >> n = if Z_lt_dec a (2 ^ n) then 0 else 1.
  Proof.
    intros a n H; break_match; [ apply lt_pow_2_shiftr; omega | ].
    destruct (Z_le_dec 0 n).
    + replace (2 * 2 ^ n) with (2 ^ (n + 1)) in *
        by (rewrite Z.pow_add_r; try omega; ring).
      pose proof (Z.shiftr_ones a (n + 1) n H).
      pose proof (Z.shiftr_le (2 ^ n) a n).
      specialize_by omega.
      replace (n + 1 - n) with 1 in * by ring.
      replace (Z.ones 1) with 1 in * by reflexivity.
      rewrite pow_2_shiftr in * by omega.
      omega.
    + assert (2 ^ n = 0) by (apply Z.pow_neg_r; omega).
      omega.
  Qed.

  Lemma shiftr_nonneg_le : forall a n, 0 <= a -> 0 <= n -> a >> n <= a.
  Proof.
    intros.
    repeat match goal with
           | [ H : _ <= _ |- _ ]
             => rewrite Z.lt_eq_cases in H
           | [ H : _ \/ _ |- _ ] => destruct H
           | _ => progress subst
           | _ => progress autorewrite with zsimplify Zshift_to_pow
           | _ => solve [ auto with zarith omega ]
           end.
  Qed.
  Hint Resolve shiftr_nonneg_le : zarith.

  Lemma log2_pred_pow2_full a : Z.log2 (Z.pred (2^a)) = Z.max 0 (Z.pred a).
  Proof.
    destruct (Z_dec 0 a) as [ [?|?] | ?].
    { rewrite Z.log2_pred_pow2 by assumption.
      apply Z.max_case_strong; omega. }
    { autorewrite with zsimplify; simpl.
      apply Z.max_case_strong; omega. }
    { subst; compute; reflexivity. }
  Qed.
  Hint Rewrite log2_pred_pow2_full : zsimplify.

  Lemma log2_up_le_full a : a <= 2^Z.log2_up a.
  Proof.
    destruct (Z_dec 1 a) as [ [ ? | ? ] | ? ];
      first [ apply Z.log2_up_spec; assumption
            | rewrite Z.log2_up_eqn0 by omega; simpl; omega ].
  Qed.

  Lemma log2_up_le_pow2_full : forall a b : Z, (0 <= b)%Z -> (a <= 2 ^ b)%Z <-> (Z.log2_up a <= b)%Z.
  Proof.
    intros a b H.
    destruct (Z_lt_le_dec 0 a); [ apply Z.log2_up_le_pow2; assumption | ].
    split; transitivity 0%Z; try omega; auto with zarith.
    rewrite Z.log2_up_eqn0 by omega.
    reflexivity.
  Qed.

  Lemma ones_lt_pow2 x y : 0 <= x <= y -> Z.ones x < 2^y.
  Proof.
    rewrite Z.ones_equiv, Z.lt_pred_le.
    auto with zarith.
  Qed.
  Hint Resolve ones_lt_pow2 : zarith.

  Lemma log2_ones_full x : Z.log2 (Z.ones x) = Z.max 0 (Z.pred x).
  Proof.
    rewrite Z.ones_equiv, log2_pred_pow2_full; reflexivity.
  Qed.
  Hint Rewrite log2_ones_full : zsimplify.

  Lemma log2_ones_lt x y : 0 < x <= y -> Z.log2 (Z.ones x) < y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_lt : zarith.

  Lemma log2_ones_le x y : 0 <= x <= y -> Z.log2 (Z.ones x) <= y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_le : zarith.

  Lemma log2_ones_lt_nonneg x y : 0 < y -> x <= y -> Z.log2 (Z.ones x) < y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_lt_nonneg : zarith.

  Lemma log2_lt_pow2_alt a b : 0 < b -> (a < 2^b <-> Z.log2 a < b).
  Proof.
    destruct (Z_lt_le_dec 0 a); auto using Z.log2_lt_pow2; [].
    rewrite Z.log2_nonpos by omega.
    split; auto with zarith; [].
    intro; eapply le_lt_trans; [ eassumption | ].
    auto with zarith.
  Qed.

  Section ZInequalities.
    Lemma land_le : forall x y, (0 <= x)%Z -> (Z.land x y <= x)%Z.
    Proof.
      intros x y H; apply Z.ldiff_le; [assumption|].
      rewrite Z.ldiff_land, Z.land_comm, Z.land_assoc.
      rewrite <- Z.land_0_l with (a := y); f_equal.
      rewrite Z.land_comm, Z.land_lnot_diag.
      reflexivity.
    Qed.

    Lemma lor_lower : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (x <= Z.lor x y)%Z.
    Proof.
      intros x y H H0; apply Z.ldiff_le; [apply Z.lor_nonneg; auto|].
      rewrite Z.ldiff_land.
      apply Z.bits_inj_iff'; intros k Hpos; apply Z.le_ge in Hpos.
      rewrite Z.testbit_0_l, Z.land_spec, Z.lnot_spec, Z.lor_spec;
        [|apply Z.ge_le; assumption].
      induction (Z.testbit x k), (Z.testbit y k); cbv; reflexivity.
    Qed.

    Lemma lor_le : forall x y z,
        (0 <= x)%Z
        -> (x <= y)%Z
        -> (y <= z)%Z
        -> (Z.lor x y <= (2 ^ Z.log2_up (z+1)) - 1)%Z.
    Proof.
      intros x y z H H0 H1; apply Z.ldiff_le.

      - apply Z.le_add_le_sub_r.
        replace 1%Z with (2 ^ 0)%Z by (cbv; reflexivity).
        rewrite Z.add_0_l.
        apply Z.pow_le_mono_r; [cbv; reflexivity|].
        apply Z.log2_up_nonneg.

      - destruct (Z_lt_dec 0 z).

        + assert (forall a, a - 1 = Z.pred a)%Z as HP by (intro; omega);
            rewrite HP, <- Z.ones_equiv; clear HP.
          apply Z.ldiff_ones_r_low; [apply Z.lor_nonneg; split; omega|].
          rewrite Z.log2_up_eqn, Z.log2_lor; try omega.
          apply Z.lt_succ_r.
          apply Z.max_case_strong; intros; apply Z.log2_le_mono; omega.

        + replace z with 0%Z by omega.
          replace y with 0%Z by omega.
          replace x with 0%Z by omega.
          cbv; reflexivity.
    Qed.

    Lemma pow2_ge_0: forall a, (0 <= 2 ^ a)%Z.
    Proof.
      intros; apply Z.pow_nonneg; omega.
    Qed.

    Lemma pow2_gt_0: forall a, (0 <= a)%Z -> (0 < 2 ^ a)%Z.
    Proof.
      intros; apply Z.pow_pos_nonneg; [|assumption]; omega.
    Qed.

    Local Ltac solve_pow2 :=
      repeat match goal with
             | [|- _ /\ _] => split
             | [|- (0 < 2 ^ _)%Z] => apply pow2_gt_0
             | [|- (0 <= 2 ^ _)%Z] => apply pow2_ge_0
             | [|- (2 ^ _ <= 2 ^ _)%Z] => apply Z.pow_le_mono_r
             | [|- (_ <= _)%Z] => omega
             | [|- (_ < _)%Z] => omega
             end.

    Lemma pow2_mod_range : forall a n m,
        (0 <= n) ->
        (n <= m) ->
        (0 <= Z.pow2_mod a n < 2 ^ m).
    Proof.
      intros; unfold Z.pow2_mod.
      rewrite Z.land_ones; [|assumption].
      split; [apply Z.mod_pos_bound, pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [apply Z.mod_pos_bound, pow2_gt_0; assumption|].
      apply Z.pow_le_mono; [|assumption].
      split; simpl; omega.
    Qed.

    Lemma shiftr_range : forall a n m,
        (0 <= n)%Z ->
        (0 <= m)%Z ->
        (0 <= a < 2 ^ (n + m))%Z ->
        (0 <= Z.shiftr a n < 2 ^ m)%Z.
    Proof.
      intros a n m H0 H1 H2; destruct H2.
      split; [apply Z.shiftr_nonneg; assumption|].
      rewrite Z.shiftr_div_pow2; [|assumption].
      apply Z.div_lt_upper_bound; [apply pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [eassumption|apply Z.eq_le_incl].
      apply Z.pow_add_r; omega.
    Qed.


    Lemma shiftr_le_mono: forall a b c d,
        (0 <= a)%Z
        -> (0 <= d)%Z
        -> (a <= c)%Z
        -> (d <= b)%Z
        -> (Z.shiftr a b <= Z.shiftr c d)%Z.
    Proof.
      intros.
      repeat rewrite Z.shiftr_div_pow2; [|omega|omega].
      etransitivity; [apply Z.div_le_compat_l | apply Z.div_le_mono]; solve_pow2.
    Qed.

    Lemma shiftl_le_mono: forall a b c d,
        (0 <= a)%Z
        -> (0 <= b)%Z
        -> (a <= c)%Z
        -> (b <= d)%Z
        -> (Z.shiftl a b <= Z.shiftl c d)%Z.
    Proof.
      intros.
      repeat rewrite Z.shiftl_mul_pow2; [|omega|omega].
      etransitivity; [apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r]; solve_pow2.
    Qed.
  End ZInequalities.

  Lemma max_log2_up x y : Z.max (Z.log2_up x) (Z.log2_up y) = Z.log2_up (Z.max x y).
  Proof. apply Z.max_monotone; intros ??; apply Z.log2_up_le_mono. Qed.
  Hint Rewrite max_log2_up : push_Zmax.
  Hint Rewrite <- max_log2_up : pull_Zmax.

  Lemma lor_bounds x y : 0 <= x -> 0 <= y
                         -> Z.max x y <= Z.lor x y <= 2^Z.log2_up (Z.max x y + 1) - 1.
  Proof.
    apply Z.max_case_strong; intros; split;
      try solve [ eauto using lor_lower, Z.le_trans, lor_le with omega
                | rewrite Z.lor_comm; eauto using lor_lower, Z.le_trans, lor_le with omega ].
  Qed.
  Lemma lor_bounds_lower x y : 0 <= x -> 0 <= y
                               -> Z.max x y <= Z.lor x y.
  Proof. intros; apply lor_bounds; assumption. Qed.
  Lemma lor_bounds_upper x y : Z.lor x y <= 2^Z.log2_up (Z.max x y + 1) - 1.
  Proof.
    pose proof (proj2 (Z.lor_neg x y)).
    destruct (Z_lt_le_dec x 0), (Z_lt_le_dec y 0);
      try solve [ intros; apply lor_bounds; assumption ];
      transitivity (2^0-1);
      try apply Z.sub_le_mono_r, Z.pow_le_mono_r, Z.log2_up_nonneg;
      simpl; omega.
  Qed.
  Lemma lor_bounds_gen_lower x y l : 0 <= x -> 0 <= y -> l <= Z.max x y
                                     -> l <= Z.lor x y.
  Proof.
    intros; etransitivity;
      solve [ apply lor_bounds; auto
            | eauto ].
  Qed.
  Lemma lor_bounds_gen_upper x y u : x <= u -> y <= u
                                     -> Z.lor x y <= 2^Z.log2_up (u + 1) - 1.
  Proof.
    intros; etransitivity; [ apply lor_bounds_upper | ].
    apply Z.sub_le_mono_r, Z.pow_le_mono_r, Z.log2_up_le_mono, Z.max_case_strong;
      omega.
  Qed.
  Lemma lor_bounds_gen x y l u : 0 <= x -> 0 <= y -> l <= Z.max x y -> x <= u -> y <= u
                                 -> l <= Z.lor x y <= 2^Z.log2_up (u + 1) - 1.
  Proof. auto using lor_bounds_gen_lower, lor_bounds_gen_upper. Qed.

  Lemma log2_up_le_full_max a : Z.max a 1 <= 2^Z.log2_up a.
  Proof.
    apply Z.max_case_strong; auto using Z.log2_up_le_full.
    intros; rewrite Z.log2_up_eqn0 by assumption; reflexivity.
  Qed.
  Lemma log2_up_le_1 a : Z.log2_up a <= 1 <-> a <= 2.
  Proof.
    pose proof (Z.log2_nonneg (Z.pred a)).
    destruct (Z_dec a 2) as [ [ ? | ? ] | ? ].
    { rewrite (proj2 (Z.log2_up_null a)) by omega; split; omega. }
    { rewrite Z.log2_up_eqn by omega.
      split; try omega; intro.
      assert (Z.log2 (Z.pred a) = 0) by omega.
      assert (Z.pred a <= 1) by (apply Z.log2_null; omega).
      omega. }
    { subst; cbv -[Z.le]; split; omega. }
  Qed.
  Lemma log2_up_1_le a : 1 <= Z.log2_up a <-> 2 <= a.
  Proof.
    pose proof (Z.log2_nonneg (Z.pred a)).
    destruct (Z_dec a 2) as [ [ ? | ? ] | ? ].
    { rewrite (proj2 (Z.log2_up_null a)) by omega; split; omega. }
    { rewrite Z.log2_up_eqn by omega; omega. }
    { subst; cbv -[Z.le]; split; omega. }
  Qed.

  Lemma shiftl_le_Proper2 y
    : Proper (Z.le ==> Z.le) (fun x => Z.shiftl x y).
  Proof.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 y) as Hx.
    intros x x' H.
    pose proof (Zle_cases 0 x) as Hy.
    pose proof (Zle_cases 0 x') as Hy'.
    destruct (0 <=? y), (0 <=? x), (0 <=? x');
      autorewrite with Zshift_to_pow;
      Z.replace_all_neg_with_pos;
      autorewrite with pull_Zopp;
      rewrite ?Z.div_opp_l_complete;
      repeat destruct (Z_zerop _);
      autorewrite with zsimplify_const pull_Zopp;
      auto with zarith;
      repeat match goal with
             | [ |- context[-?x - ?y] ]
               => replace (-x - y) with (-(x + y)) by omega
             | _ => rewrite <- Z.opp_le_mono
             | _ => rewrite <- Z.add_le_mono_r
             | _ => solve [ auto with zarith ]
             | [ |- ?x <= ?y + 1 ]
               => cut (x <= y); [ omega | solve [ auto with zarith ] ]
             | [ |- -_ <= _ ]
               => solve [ transitivity (-0); auto with zarith ]
             end.
    { repeat match goal with H : context[_ mod _] |- _ => revert H end;
        Z.div_mod_to_quot_rem; nia. }
  Qed.

  Lemma shiftl_le_Proper1 x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (0 <=? x) ==> Z.le) (Z.shiftl x).
  Proof.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 x) as Hx.
    intros y y' H.
    pose proof (Zle_cases 0 y) as Hy.
    pose proof (Zle_cases 0 y') as Hy'.
    destruct (0 <=? x), (0 <=? y), (0 <=? y'); subst R; cbv beta iota in *;
      autorewrite with Zshift_to_pow;
      Z.replace_all_neg_with_pos;
      autorewrite with pull_Zopp;
      rewrite ?Z.div_opp_l_complete;
      repeat destruct (Z_zerop _);
      autorewrite with zsimplify_const pull_Zopp;
      auto with zarith;
      repeat match goal with
             | [ |- context[-?x - ?y] ]
               => replace (-x - y) with (-(x + y)) by omega
             | _ => rewrite <- Z.opp_le_mono
             | _ => rewrite <- Z.add_le_mono_r
             | _ => solve [ auto with zarith ]
             | [ |- ?x <= ?y + 1 ]
               => cut (x <= y); [ omega | solve [ auto with zarith ] ]
             | [ |- context[2^?x] ]
               => lazymatch goal with
                  | [ H : 1 < 2^x |- _ ] => fail
                  | [ H : 0 < 2^x |- _ ] => fail
                  | [ H : 0 <= 2^x |- _ ] => fail
                  | _ => first [ assert (1 < 2^x) by auto with zarith
                               | assert (0 < 2^x) by auto with zarith
                               | assert (0 <= 2^x) by auto with zarith ]
                  end
             | [ H : ?x <= ?y |- _ ]
               => is_var x; is_var y;
                    lazymatch goal with
                    | [ H : 2^x <= 2^y |- _ ] => fail
                    | [ H : 2^x < 2^y |- _ ] => fail
                    | _ => assert (2^x <= 2^y) by auto with zarith
                    end
             | [ H : ?x <= ?y, H' : ?f ?x = ?k, H'' : ?f ?y <> ?k |- _ ]
               => let Hn := fresh in
                  assert (Hn : x <> y) by congruence;
                    assert (x < y) by omega; clear H Hn
             | [ H : ?x <= ?y, H' : ?f ?x <> ?k, H'' : ?f ?y = ?k |- _ ]
               => let Hn := fresh in
                  assert (Hn : x <> y) by congruence;
                    assert (x < y) by omega; clear H Hn
             | _ => solve [ repeat match goal with H : context[_ mod _] |- _ => revert H end;
                            Z.div_mod_to_quot_rem; subst;
                            lazymatch goal with
                            | [ |- _ <= (?a * ?q + ?r) * ?q' ]
                              => transitivity (q * (a * q') + r * q');
                                 [ assert (0 < a * q') by nia; nia
                                 | nia ]
                            end ]
             end.
    { replace y' with (y + (y' - y)) by omega.
      rewrite Z.pow_add_r, <- Zdiv_Zdiv by auto with zarith.
      assert (y < y') by (assert (y <> y') by congruence; omega).
      assert (1 < 2^(y'-y)) by auto with zarith.
      assert (0 < x / 2^y)
        by (repeat match goal with H : context[_ mod _] |- _ => revert H end;
            Z.div_mod_to_quot_rem; nia).
      assert (2^y <= x)
        by (repeat match goal with H : context[_ / _] |- _ => revert H end;
            Z.div_mod_to_quot_rem; nia).
      match goal with
      | [ |- ?x + 1 <= ?y ] => cut (x < y); [ omega | ]
      end.
      auto with zarith. }
  Qed.

  Lemma shiftr_le_Proper2 y
    : Proper (Z.le ==> Z.le) (fun x => Z.shiftr x y).
  Proof. apply shiftl_le_Proper2. Qed.

  Lemma shiftr_le_Proper1 x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (x <? 0) ==> Z.le) (Z.shiftr x).
  Proof.
    subst R; intros y y' H'; unfold Z.shiftr; apply shiftl_le_Proper1.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 x).
    pose proof (Zlt_cases x 0).
    destruct (0 <=? x), (x <? 0); try omega.
  Qed.
End Z.

Module N2Z.
  Lemma inj_land n m : Z.of_N (N.land n m) = Z.land (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.
  Hint Rewrite inj_land : push_Zof_N.
  Hint Rewrite <- inj_land : pull_Zof_N.

  Lemma inj_lor n m : Z.of_N (N.lor n m) = Z.lor (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.
  Hint Rewrite inj_lor : push_Zof_N.
  Hint Rewrite <- inj_lor : pull_Zof_N.

  Lemma inj_shiftl: forall x y, Z.of_N (N.shiftl x y) = Z.shiftl (Z.of_N x) (Z.of_N y).
  Proof.
    intros x y.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftl_spec; [|assumption].

    assert ((Z.to_N k) >= y \/ (Z.to_N k) < y)%N as g by (
        unfold N.ge, N.lt; induction (N.compare (Z.to_N k) y); [left|auto|left];
        intro H; inversion H).

    destruct g as [g|g];
    [ rewrite N.shiftl_spec_high; [|apply N2Z.inj_le; rewrite Z2N.id|apply N.ge_le]
    | rewrite N.shiftl_spec_low]; try assumption.

    - rewrite <- N2Z.inj_testbit; f_equal.
        rewrite N2Z.inj_sub, Z2N.id; [reflexivity|assumption|apply N.ge_le; assumption].

    - apply N2Z.inj_lt in g.
        rewrite Z2N.id in g; [symmetry|assumption].
        apply Z.testbit_neg_r; omega.
  Qed.
  Hint Rewrite inj_shiftl : push_Zof_N.
  Hint Rewrite <- inj_shiftl : pull_Zof_N.

  Lemma inj_shiftr: forall x y, Z.of_N (N.shiftr x y) = Z.shiftr (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftr_spec, N.shiftr_spec; [|apply N2Z.inj_le; rewrite Z2N.id|]; try assumption.
    rewrite <- N2Z.inj_testbit; f_equal.
    rewrite N2Z.inj_add; f_equal.
    apply Z2N.id; assumption.
  Qed.
  Hint Rewrite inj_shiftr : push_Zof_N.
  Hint Rewrite <- inj_shiftr : pull_Zof_N.
End N2Z.

Module Export BoundsTactics.
  Ltac prime_bound := Z.prime_bound.
  Ltac zero_bounds := Z.zero_bounds.
End BoundsTactics.
