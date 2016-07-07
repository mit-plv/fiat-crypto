Require Import Coq.ZArith.Zpower Coq.ZArith.Znumtheory Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.micromega.Psatz Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Notations.
Require Import Coq.Lists.List.
Import Nat.
Local Open Scope Z.

Infix ">>" := Z.shiftr : Z_scope.
Infix "<<" := Z.shiftl : Z_scope.
Infix "&" := Z.land : Z_scope.

Hint Extern 1 => lia : lia.
Hint Extern 1 => lra : lra.
Hint Extern 1 => nia : nia.
Hint Extern 1 => omega : omega.
Hint Resolve Z.log2_nonneg Z.div_small Z.mod_small Z.pow_neg_r Z.pow_0_l : zarith.
Hint Resolve (fun a b H => proj1 (Z.mod_pos_bound a b H)) (fun a b H => proj2 (Z.mod_pos_bound a b H)) : zarith.

(** Only hints that are always safe to apply (i.e., reversible), and
    which can reasonably be said to "simplify" the goal, should go in
    this database. *)
Create HintDb zsimplify discriminated.
Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r : zsimplify.
Hint Rewrite Z.div_mul Z.div_1_l Z.div_same Z.mod_same Z.div_small Z.mod_small Z.div_add Z.div_add_l Z.mod_add using lia : zsimplify.

(** "push" means transform [-f x] to [f (-x)]; "pull" means go the other way *)
Create HintDb push_Zopp discriminated.
Create HintDb pull_Zopp discriminated.
Hint Rewrite Z.div_opp_l_nz Z.div_opp_l_z using lia : pull_Zopp.
Hint Rewrite Z.mul_opp_l : pull_Zopp.
Hint Rewrite <- Z.opp_add_distr : pull_Zopp.
Hint Rewrite <- Z.div_opp_l_nz Z.div_opp_l_z using lia : push_Zopp.
Hint Rewrite <- Z.mul_opp_l : push_Zopp.
Hint Rewrite Z.opp_add_distr : push_Zopp.

Create HintDb push_Zmul discriminated.
Create HintDb pull_Zmul discriminated.
Hint Rewrite Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : push_Zmul.
Hint Rewrite <- Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : pull_Zmul.

(** For the occasional lemma that can remove the use of [Z.div] *)
Create HintDb zstrip_div.
Hint Rewrite Z.div_small_iff using lia : zstrip_div.

(** It's not clear that [mod] is much easier for [lia] than [Z.div],
    so we separate out the transformations between [mod] and [div].
    We'll put, e.g., [mul_div_eq] into it below. *)
Create HintDb zstrip_div.

Module Z.
  Definition pow2_mod n i := (n & (Z.ones i)).

  Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
  Proof. intros; omega. Qed.

  Hint Resolve positive_is_nonzero : zarith.

  Lemma div_positive_gt_0 : forall a b, a > 0 -> b > 0 -> a mod b = 0 ->
    a / b > 0.
  Proof.
    intros; rewrite Z.gt_lt_iff.
    apply Z.div_str_pos.
    split; intuition.
    apply Z.divide_pos_le; try (apply Zmod_divide); omega.
  Qed.

  Lemma elim_mod : forall a b m, a = b -> a mod m = b mod m.
  Proof. intros; subst; auto. Qed.

  Hint Resolve elim_mod : zarith.

  Lemma mod_add_l : forall a b c, b <> 0 -> (a * b + c) mod b = c mod b.
  Proof. intros; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_l using lia : zsimplify.

  Lemma mod_add' : forall a b c, b <> 0 -> (a + b * c) mod b = a mod b.
  Proof. intros; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l' : forall a b c, a <> 0 -> (a * b + c) mod a = c mod a.
  Proof. intros; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add' mod_add_l' using lia : zsimplify.

  Lemma pos_pow_nat_pos : forall x n,
    Z.pos x ^ Z.of_nat n > 0.
  Proof.
    do 2 (intros; induction n; subst; simpl in *; auto with zarith).
    rewrite <- Pos.add_1_r, Zpower_pos_is_exp.
    apply Zmult_gt_0_compat; auto; reflexivity.
  Qed.

  Lemma div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul; auto. Qed.
  Hint Rewrite div_mul' using lia : zsimplify.

  (** TODO: Should we get rid of this duplicate? *)
  Notation gt0_neq0 := positive_is_nonzero (only parsing).

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

  Lemma pow_Zpow : forall a n : nat, Z.of_nat (a ^ n) = Z.of_nat a ^ Z.of_nat n.
  Proof with auto using Zle_0_nat, Z.pow_nonneg.
    intros; apply Z2Nat.inj...
    rewrite <- pow_Z2N_Zpow, !Nat2Z.id...
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

  Ltac divide_exists_mul := let k := fresh "k" in
  match goal with
  | [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H; destruct H as [k H]
  | [ |- (?a | ?b) ] => apply Z.mod_divide; try apply Zmod_divides
  end; (omega || auto).

  Lemma divide_mul_div: forall a b c (a_nonzero : a <> 0) (c_nonzero : c <> 0),
    (a | b * (a / c)) -> (c | a) -> (c | b).
  Proof.
    intros ? ? ? ? ? divide_a divide_c_a; do 2 divide_exists_mul.
    rewrite divide_c_a in divide_a.
    rewrite div_mul' in divide_a by auto.
    replace (b * k) with (k * b) in divide_a by ring.
    replace (c * k * k0) with (k * (k0 * c)) in divide_a by ring.
    rewrite Z.mul_cancel_l in divide_a by (intuition; rewrite H in divide_c_a; ring_simplify in divide_a; intuition).
    eapply Zdivide_intro; eauto.
  Qed.

  Lemma divide2_even_iff : forall n, (2 | n) <-> Z.even n = true.
  Proof.
    intro; split. {
      intro divide2_n.
      divide_exists_mul; [ | pose proof (Z.mod_pos_bound n 2); omega].
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

  Lemma mul_div_eq : forall a m, m > 0 -> m * (a / m) = (a - a mod m).
  Proof.
    intros.
    rewrite (Z_div_mod_eq a m) at 2 by auto.
    ring.
  Qed.

  Lemma mul_div_eq' : (forall a m, m > 0 -> (a / m) * m = (a - a mod m))%Z.
  Proof.
    intros.
    rewrite (Z_div_mod_eq a m) at 2 by auto.
    ring.
  Qed.

  Hint Rewrite mul_div_eq mul_div_eq' using lia : zdiv_to_mod.
  Hint Rewrite <- mul_div_eq' using lia : zmod_to_div.

  Ltac prime_bound := match goal with
  | [ H : prime ?p |- _ ] => pose proof (prime_ge_2 p H); try omega
  end.

  Lemma testbit_low : forall n x i, (0 <= i < n) ->
    Z.testbit x i = Z.testbit (Z.land x (Z.ones n)) i.
  Proof.
    intros.
    rewrite Z.land_ones by omega.
    symmetry.
    apply Z.mod_pow2_bits_low.
    omega.
  Qed.


  Lemma testbit_add_shiftl_low : forall i, (0 <= i) -> forall a b n, (i < n) ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit a i.
  Proof.
    intros.
    erewrite Z.testbit_low; eauto.
    rewrite Z.land_ones, Z.shiftl_mul_pow2 by omega.
    rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 n); omega).
    auto using Z.mod_pow2_bits_low.
  Qed.

  Lemma mod_div_eq0 : forall a b, 0 < b -> (a mod b) / b = 0.
  Proof.
    intros.
    apply Z.div_small.
    auto using Z.mod_pos_bound.
  Qed.
  Hint Rewrite mod_div_eq0 using lia : zsimplify.

  Lemma shiftr_add_shiftl_high : forall n m a b, 0 <= n <= m -> 0 <= a < 2 ^ n ->
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

  Lemma shiftr_add_shiftl_low : forall n m a b, 0 <= m <= n -> 0 <= a < 2 ^ n ->
    Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr a m + Z.shiftr b (m - n).
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2, Z.shiftr_mul_pow2 by omega.
    replace (2 ^ n) with (2 ^ (n - m) * 2 ^ m) by
      (rewrite <-Z.pow_add_r by omega; f_equal; ring).
    rewrite Z.mul_assoc, Z.div_add by (apply Z.pow_nonzero; omega).
    repeat f_equal; ring.
  Qed.

  Lemma testbit_add_shiftl_high : forall i, (0 <= i) -> forall a b n, (0 <= n <= i) ->
    0 <= a < 2 ^ n ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit b (i - n).
  Proof.
    intros ? ?.
    apply natlike_ind with (x := i); intros; try assumption;
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

  Lemma land_add_land : forall n m a b, (m <= n)%nat ->
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


  Definition shiftl_by n a := Z.shiftl a n.

  Lemma shiftl_by_mul_pow2 : forall n a, 0 <= n -> Z.mul (2 ^ n) a = Z.shiftl_by n a.
  Proof.
    intros.
    unfold Z.shiftl_by.
    rewrite Z.shiftl_mul_pow2 by assumption.
    apply Z.mul_comm.
  Qed.

  Lemma map_shiftl : forall n l, 0 <= n -> map (Z.mul (2 ^ n)) l = map (Z.shiftl_by n) l.
  Proof.
    intros; induction l; auto using Z.shiftl_by_mul_pow2.
    simpl.
    rewrite IHl.
    f_equal.
    apply Z.shiftl_by_mul_pow2.
    assumption.
  Qed.

  Lemma odd_mod : forall a b, (b <> 0)%Z ->
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
  Hint Rewrite mod_same_pow using lia : zsimplify.

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

  Lemma ones_pred : forall i, 0 < i -> Z.ones (Z.pred i) = Z.shiftr (Z.ones i) 1.
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

  Lemma shiftr_ones' : forall a n, 0 <= a < 2 ^ n -> forall i, (0 <= i) ->
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

  Lemma lor_shiftl : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor a (Z.shiftl b n) = a + (Z.shiftl b n).
  Proof.
    intros.
    apply Z.bits_inj'; intros t ?.
    rewrite Z.lor_spec, Z.shiftl_spec by assumption.
    destruct (Z_lt_dec t n).
    + rewrite testbit_add_shiftl_low by omega.
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

  Hint Extern 1 => progress zero_bounds : zero_bounds.

  Lemma ones_nonneg : forall i, (0 <= i) -> 0 <= Z.ones i.
  Proof.
    apply natlike_ind.
    + unfold Z.ones. simpl; omega.
    + intros.
      rewrite Z.ones_succ by assumption.
      zero_bounds.
  Qed.

  Lemma ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
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

  Lemma land_upper_bound_l : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= a.
  Proof.
    intros.
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
    induction l; intros ? lower_bound In_list; [cbv [In] in *; intuition | ].
    simpl.
    destruct (in_inv In_list); subst.
    + apply Z.le_max_l.
    + etransitivity.
      - apply IHl; auto; intuition.
      - apply Z.le_max_r.
  Qed.

  Lemma le_fold_right_max_initial : forall low l, low <= fold_right Z.max low l.
  Proof.
    induction l; intros; try reflexivity.
    etransitivity; [ apply IHl | apply Z.le_max_r ].
  Qed.

  Ltac ltb_to_lt :=
    repeat match goal with
           | [ H : (?x <? ?y) = ?b |- _ ]
             => let H' := fresh in
                rename H into H';
                pose proof (Zlt_cases x y) as H;
                rewrite H' in H;
                clear H'
           end.

  Ltac compare_to_sgn :=
    repeat match goal with
           | [ H : _ |- _ ] => progress rewrite <- ?Z.sgn_neg_iff, <- ?Z.sgn_pos_iff, <- ?Z.sgn_null_iff in H
           | _ => progress rewrite <- ?Z.sgn_neg_iff, <- ?Z.sgn_pos_iff, <- ?Z.sgn_null_iff
           end.

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
    repeat first [ progress intuition
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

  Lemma two_times_x_minus_x x : 2 * x - x = x.
  Proof. lia. Qed.

  Lemma mul_div_le x y z
        (Hx : 0 <= x) (Hy : 0 <= y) (Hz : 0 < z)
        (Hyz : y <= z)
    : x * y / z <= x.
  Proof.
    transitivity (x * z / z); [ | rewrite Z.div_mul by lia; lia ].
    apply Z_div_le; nia.
  Qed.

  Lemma div_mul_diff a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * a / b - c * (a / b) <= c.
  Proof.
    pose proof (Z.mod_pos_bound a b).
    etransitivity; [ | apply (mul_div_le c (a mod b) b); lia ].
    rewrite (Z_div_mod_eq a b) at 1 by lia.
    rewrite Z.mul_add_distr_l.
    replace (c * (b * (a / b))) with ((c * (a / b)) * b) by lia.
    rewrite Z.div_add_l by lia.
    lia.
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

  (** * [Z.simplify_fractions_le] *)
  (** The culmination of this series of tactics,
      [Z.simplify_fractions_le], will use the fact that [a * (b / c) <=
      (a * b) / c], and do some reasoning modulo associativity and
      commutativity in [Z] to perform such a reduction.  It may leave
      over goals if it cannot prove that some denominators are non-zero.
      If the rewrite [a * (b / c)] → [(a * b) / c] is safe to do on the
      LHS of the goal, this tactic should not turn a solvable goal into
      an unsolvable one.

      After running, the tactic does some basic rewriting to simplify
      fractions, e.g., that [a * b / b = a]. *)
  Ltac split_sums_step :=
    match goal with
    | [ |- _ + _ <= _ ]
      => etransitivity; [ eapply Z.add_le_mono | ]
    | [ |- _ - _ <= _ ]
      => etransitivity; [ eapply Z.sub_le_mono | ]
    end.
  Ltac split_sums :=
    try (split_sums_step; [ split_sums.. | ]).
  Ltac pre_reorder_fractions_step :=
    match goal with
    | [ |- context[?x / ?y * ?z] ]
      => rewrite (Z.mul_comm (x / y) z)
    | _ => let LHS := match goal with |- ?LHS <= ?RHS => LHS end in
           match LHS with
           | context G[?x * (?y / ?z)]
             => let G' := context G[(x * y) / z] in
                transitivity G'
           end
    end.
  Ltac pre_reorder_fractions :=
    try first [ split_sums_step; [ pre_reorder_fractions.. | ]
              | pre_reorder_fractions_step; [ .. | pre_reorder_fractions ] ].
  Ltac split_comparison :=
    match goal with
    | [ |- ?x <= ?x ] => reflexivity
    | [ H : _ >= _ |- _ ]
      => apply Z.ge_le_iff in H
    | [ |- ?x * ?y <= ?z * ?w ]
      => lazymatch goal with
         | [ H : 0 <= x |- _ ] => idtac
         | [ H : x < 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0)
         end;
         [ ..
         | lazymatch goal with
           | [ H : 0 <= y |- _ ] => idtac
           | [ H : y < 0 |- _ ] => fail
           | _ => destruct (Z_lt_le_dec y 0)
           end;
           [ ..
           | apply Zmult_le_compat; [ | | assumption | assumption ] ] ]
    | [ |- ?x / ?y <= ?z / ?y ]
      => lazymatch goal with
         | [ H : 0 < y |- _ ] => idtac
         | [ H : y <= 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec 0 y)
         end;
         [ apply Z_div_le; [ apply Z.gt_lt_iff; assumption | ]
         | .. ]
    | [ |- ?x / ?y <= ?x / ?z ]
      => lazymatch goal with
         | [ H : 0 <= x |- _ ] => idtac
         | [ H : x < 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0)
         end;
         [ ..
         | lazymatch goal with
           | [ H : 0 < z |- _ ] => idtac
           | [ H : z <= 0 |- _ ] => fail
           | _ => destruct (Z_lt_le_dec 0 z)
           end;
           [ apply Z.div_le_compat_l; [ assumption | split; [ assumption | ] ]
           | .. ] ]
    | [ |- _ + _ <= _ + _ ]
      => apply Z.add_le_mono
    | [ |- _ - _ <= _ - _ ]
      => apply Z.sub_le_mono
    | [ |- ?x * (?y / ?z) <= (?x * ?y) / ?z ]
      => apply Z.div_mul_le
    end.
  Ltac split_comparison_fin_step :=
    match goal with
    | _ => assumption
    | _ => lia
    | _ => progress subst
    | [ H : ?n * ?m < 0 |- _ ]
      => apply (proj1 (Z.lt_mul_0 n m)) in H; destruct H as [[??]|[??]]
    | [ H : ?n / ?m < 0 |- _ ]
      => apply (proj1 (lt_div_0 n m)) in H; destruct H as [[[??]|[??]]?]
    | [ H : (?x^?y) <= ?n < _, H' : ?n < 0 |- _ ]
      => assert (0 <= x^y) by zero_bounds; lia
    | [ H : (?x^?y) < 0 |- _ ]
      => assert (0 <= x^y) by zero_bounds; lia
    | [ H : (?x^?y) <= 0 |- _ ]
      => let H' := fresh in
         assert (H' : 0 <= x^y) by zero_bounds;
         assert (x^y = 0) by lia;
         clear H H'
    | [ H : _^_ = 0 |- _ ]
      => apply Z.pow_eq_0_iff in H; destruct H as [?|[??]]
    | [ H : 0 <= ?x, H' : ?x - 1 < 0 |- _ ]
      => assert (x = 0) by lia; clear H H'
    | [ |- ?x <= ?y ] => is_evar x; reflexivity
    | [ |- ?x <= ?y ] => is_evar y; reflexivity
    end.
  Ltac split_comparison_fin := repeat split_comparison_fin_step.
  Ltac simplify_fractions_step :=
    match goal with
    | _ => rewrite Z.div_mul by (try apply Z.pow_nonzero; zero_bounds)
    | [ |- context[?x * ?y / ?x] ]
      => rewrite (Z.mul_comm x y)
    | [ |- ?x <= ?x ] => reflexivity
    end.
  Ltac simplify_fractions := repeat simplify_fractions_step.
  Ltac simplify_fractions_le :=
    pre_reorder_fractions;
    [ repeat split_comparison; split_comparison_fin; zero_bounds..
    | simplify_fractions ].

  Lemma log2_nonneg' n a : n <= 0 -> n <= Z.log2 a.
  Proof.
    intros; transitivity 0; auto with zarith.
  Qed.

  Hint Resolve log2_nonneg' : zarith.

  (** We create separate databases for two directions of transformations
      involving [Z.log2]; combining them leads to loops. *)
  (* for hints that take in hypotheses of type [log2 _], and spit out conclusions of type [_ ^ _] *)
  Create HintDb hyp_log2.

  (* for hints that take in hypotheses of type [_ ^ _], and spit out conclusions of type [log2 _] *)
  Create HintDb concl_log2.

  Hint Resolve (fun a b H => proj1 (Z.log2_lt_pow2 a b H)) (fun a b H => proj1 (Z.log2_le_pow2 a b H)) : concl_log2.
  Hint Resolve (fun a b H => proj2 (Z.log2_lt_pow2 a b H)) (fun a b H => proj2 (Z.log2_le_pow2 a b H)) : hyp_log2.

  Lemma le_lt_to_log2 x y z : 0 <= z -> 0 < y -> 2^x <= y < 2^z -> x <= Z.log2 y < z.
  Proof.
    destruct (Z_le_gt_dec 0 x); auto with concl_log2 lia.
  Qed.

  Lemma div_x_y_x x y : 0 < x -> 0 < y -> x / y / x = 1 / y.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm y x), <- Z.div_div, Z.div_same by lia.
    reflexivity.
  Qed.

  Hint Rewrite div_x_y_x using lia : zsimplify.

  Lemma mod_opp_l_z_iff a b (H : b <> 0) : a mod b = 0 <-> (-a) mod b = 0.
  Proof.
    split; intro H'; apply Z.mod_opp_l_z in H'; rewrite ?Z.opp_involutive in H'; assumption.
  Qed.

  Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
  Proof. lia. Qed.

  Hint Rewrite <- mod_opp_l_z_iff using lia : zsimplify.
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

  Hint Rewrite Z.div_opp_l_complete using lia : pull_Zopp.
  Hint Rewrite Z.div_opp_l_complete' using lia : push_Zopp.

  Lemma div_opp a : a <> 0 -> -a / a = -1.
  Proof.
    intros; autorewrite with pull_Zopp zsimplify; lia.
  Qed.

  Hint Rewrite Z.div_opp using lia : zsimplify.

  Lemma div_sub_1_0 x : x > 0 -> (x - 1) / x = 0.
  Proof. auto with zarith lia. Qed.

  Hint Rewrite div_sub_1_0 using lia : zsimplify.

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

  Hint Rewrite Z.sub_pos_bound_div_eq Z.add_opp_pos_bound_div_eq using lia : zstrip_div.

  Lemma div_small_sym a b : 0 <= a < b -> 0 = a / b.
  Proof. intros; symmetry; apply Z.div_small; assumption. Qed.

  Lemma mod_small_sym a b : 0 <= a < b -> a = a mod b.
  Proof. intros; symmetry; apply Z.mod_small; assumption. Qed.

  Hint Resolve div_small_sym mod_small_sym : zarith.

  Lemma div_add' a b c : c <> 0 -> (a + c * b) / c = a / c + b.
  Proof. intro; rewrite <- Z.div_add, (Z.mul_comm c); try lia. Qed.

  Lemma div_add_l' a b c : b <> 0 -> (b * a + c) / b = a + c / b.
  Proof. intro; rewrite <- Z.div_add_l, (Z.mul_comm b); lia. Qed.

  Hint Rewrite div_add_l' div_add' using lia : zsimplify.

  Lemma div_add_sub_l a b c d : b <> 0 -> (a * b + c - d) / b = a + (c - d) / b.
  Proof. rewrite <- Z.add_sub_assoc; apply Z.div_add_l. Qed.

  Lemma div_add_sub_l' a b c d : b <> 0 -> (b * a + c - d) / b = a + (c - d) / b.
  Proof. rewrite <- Z.add_sub_assoc; apply Z.div_add_l'. Qed.

  Lemma div_add_sub a b c d : c <> 0 -> (a + b * c - d) / c = (a - d) / c + b.
  Proof. rewrite (Z.add_comm _ (_ * _)), (Z.add_comm (_ / _)); apply Z.div_add_sub_l. Qed.

  Lemma div_add_sub' a b c d : c <> 0 -> (a + c * b - d) / c = (a - d) / c + b.
  Proof. rewrite (Z.add_comm _ (_ * _)), (Z.add_comm (_ / _)); apply Z.div_add_sub_l'. Qed.

  Hint Rewrite Z.div_add_sub Z.div_add_sub' Z.div_add_sub_l Z.div_add_sub_l' using lia : zsimplify.

  Lemma div_mul_skip a b k : 0 < b -> 0 < k -> a * b / k / b = a / k.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm k), <- Z.div_div by lia.
    autorewrite with zsimplify; reflexivity.
  Qed.

  Lemma div_mul_skip' a b k : 0 < b -> 0 < k -> b * a / k / b = a / k.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm k), <- Z.div_div by lia.
    autorewrite with zsimplify; reflexivity.
  Qed.

  Hint Rewrite Z.div_mul_skip Z.div_mul_skip' using lia : zsimplify.
End Z.

Module Export BoundsTactics.
  Ltac prime_bound := Z.prime_bound.
  Ltac zero_bounds := Z.zero_bounds.
End BoundsTactics.
