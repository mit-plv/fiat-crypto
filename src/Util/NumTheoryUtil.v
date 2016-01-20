Require Import Zpower Znumtheory ZArith.ZArith ZArith.Zdiv.
Require Import Omega NPeano Arith.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil.
Require Import Coqprime.Zp.
Require Import VerdiTactics.
Local Open Scope Z.

(* TODO : integrate Andres's Fermat's little theorem proof *)
Lemma fermat_little: forall (a p : Z) (prime_p : prime p),
  a mod p <> 0 -> a ^ (p - 1) mod p = 1.
Admitted.

Ltac prime_bound := match goal with
| H : prime ?p |- _ => pose proof (prime_ge_2 p H); try omega
end.

Lemma prime_minus1_div2_nonneg : forall (x p : Z) (prime_p : prime p),
  x * 2 + 1 = p -> 0 < x.
Proof.
  intros; prime_bound.
Qed.

Lemma squared_fermat_little: forall (a x p : Z) (prime_p : prime p),
  x * 2 + 1 = p -> a mod p <> 0 -> (a * a) ^ x mod p = 1.
Proof.
  intros.
  rewrite <- Z.pow_2_r.
  rewrite <- Z.pow_mul_r by
    (pose proof (prime_minus1_div2_nonneg x p prime_p H); omega).
  rewrite Z.mul_comm.
  replace (x * 2) with (x * 2 + 1 - 1) by omega.
  rewrite H.
  apply fermat_little; auto.
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

Lemma euler_criterion_reverse : forall (a x p : Z) (prime_p : prime p),
  (x * 2 + 1 = p) -> (a mod p <> 0) ->
  (exists b, b * b mod p = a mod p) -> (a ^ x mod p = 1).
Proof.
  intros.
  destruct H1.
  assert (x0 mod p <> 0). {
    intuition.
    assert (2 > 0) by omega.
    assert (p > 1) by prime_bound.
    pose proof (mod_exp_0 x0 2 p H3 H4 H2); clear H3; clear H4.
    rewrite Z.pow_2_r in H5.
    rewrite H5 in H1.
    intuition.
  }
  pose proof (squared_fermat_little x0 x p prime_p H H2).
  assert (0 <= x) by (pose proof (prime_minus1_div2_nonneg x p prime_p H); omega).
  assert (p <> 0) by prime_bound.
  rewrite mod_pow by auto.
  pose proof (mod_pow (x0 * x0) p x H4 H5).
  rewrite H3 in H6.
  rewrite H1 in H6.
  auto.
Qed.
(*
Fixpoint order_mod' y p i r :=
  match i with
  | O => r
  | S i' => if (Zeq_bool (y ^ (Z.of_nat i) mod p) 1)
            then order_mod' y p i' (Z.of_nat i)
            else order_mod' y p i' r
  end.

Definition order_mod y p := order_mod' y p (Z.to_nat (p - 2)) (p - 1).

Lemma order_mod'_le_r : forall y p i r, Z.of_nat i <= r ->
  order_mod' y p i r <= r.
Proof.
  induction i; intros; try (simpl; omega).
  unfold order_mod'; fold order_mod'.
  assert (Z.of_nat i <= Z.of_nat (S i)) by (rewrite <- Nat2Z.inj_le; omega).
  break_if. {
    specialize (IHi (Z.of_nat (S i)) H0).
    omega.
  } {
    apply IHi.
    omega.
  }
Qed.

Lemma order_mod'_pos : forall y p i r, 1 <= r -> 1 <= order_mod' y p i r.
Proof.
  induction i; intros; auto.
  unfold order_mod'; fold order_mod'.
  break_if; apply IHi; auto.
  replace 1 with (Z.of_nat 1) by auto.
  rewrite <- Nat2Z.inj_le.
  pose proof (lt_0_Sn i); omega.
Qed.

Lemma order_mod_bounds : forall y p (prime_p : prime p),
  1 <= order_mod y p <= p - 1.
Proof.
  unfold order_mod; split; intros. {
    apply order_mod'_pos; prime_bound.
  } {
    apply order_mod'_le_r.
    rewrite Z2Nat.id; prime_bound; omega.
  }
Qed.

Lemma order_mod'_id : forall y p i r,
  y ^ r mod p = 1 ->
  y ^ (order_mod' y p i r) mod p = 1.
Proof.
  induction i; intros; [simpl; auto |].
  unfold order_mod'; fold order_mod'.
  break_if; auto.
  apply IHi.
  apply Zeq_bool_eq; auto.
Qed.

Lemma order_mod_id : forall y p (prime_p : prime p), (y mod p <> 0) -> y ^ (order_mod y p) mod p = 1.
Proof.
  intros.
  unfold order_mod; apply order_mod'_id.
  apply fermat_little; auto.
Qed.

Lemma order_mod'_upper_bound : forall x y p i r, 1 <= x <= Z.of_nat i ->
  (Z.of_nat i <= r) -> (y ^ x mod p = 1) -> order_mod' y p i r <= x.
Proof.
  induction i; intros; try (simpl in H; omega).
  unfold order_mod'; fold order_mod'.
  assert (Z.of_nat i <= Z.of_nat (S i)) by (rewrite <- Nat2Z.inj_le; omega).
  break_if. {
    specialize (IHi (Z.of_nat (S i))).
    destruct (Z.eq_dec x (Z.of_nat (S i))). {
      rewrite e.
      apply order_mod'_le_r; auto.
    } {
      destruct H.
      rewrite Nat2Z.inj_succ in H3.
      apply (Z.le_succ_r x (Z.of_nat i)) in H3.
      destruct H3; intuition.
      rewrite Nat2Z.inj_succ.
      rewrite H3.
      apply order_mod'_le_r.
      omega.
    }
  } {
    destruct H.
    apply Z.le_lteq in H3; destruct H3. {
      rewrite Nat2Z.inj_succ in H3.
      apply IHi; omega.
    } {
      exfalso.
      destruct H3.
      apply Zeq_is_eq_bool in H1.
      rewrite Heqb in H1.
      intuition.
    }
  }
Qed.

Lemma order_mod_upper_bound : forall x y p (prime_p : prime p),
  (1 <= x <= p - 2) ->
  (y ^ x mod p = 1) -> order_mod y p <= x.
Proof.
  unfold order_mod; intros.
  apply order_mod'_upper_bound; (rewrite Z2Nat.id; omega) || prime_bound.
Qed.

Lemma order_mod_lowest : forall x y p (prime_p : prime p),
  1 <= x < order_mod y p -> y ^ x mod p <> 1.
Proof.
  intros.
  intuition.
  pose proof (order_mod_upper_bound x y p prime_p).
  assert (1 <= x <= p - 2) as x_bounds. {
    pose proof (order_mod_bounds y p prime_p).
    omega.
  }
  specialize (H x_bounds H0).
  omega.
Qed.

Lemma pow_mod_order : forall x y p (prime_p : prime p), 1 <= x ->
  y ^ x mod p = 1 -> y ^ (x mod (order_mod y p)) mod p = 1.
Proof.
  intros.
  remember (order_mod y p) as ord.
  pose proof (order_mod_bounds y p prime_p).
  assert (0 <= x / ord) by (apply Z.div_pos; omega).
  assert (y mod p <> 0) by (intuition; apply (mod_exp_0 _ x) in H3; prime_bound).
  rewrite (Z_div_mod_eq x ord) in H0 by omega.
  rewrite Z.pow_add_r in H0 by (try apply Z.mul_nonneg_nonneg;
    try apply Z.mod_pos_bound; omega).
  rewrite Zmult_mod in H0.
  rewrite Z.pow_mul_r in H0 by (try apply Z.mod_pos_bound; omega).
  rewrite mod_pow in H0 by (prime_bound || auto).
  rewrite Heqord in H0 at 1.
  rewrite order_mod_id in H0; auto.
  rewrite Z.pow_1_l in H0 by auto.
  rewrite Z.mod_1_l in H0 by prime_bound.
  rewrite Z.mul_1_l in H0.
  rewrite Z.mod_mod in H0 by prime_bound.
  auto.
Qed.

Lemma order_mod_divide : forall x y p (prime_p : prime p), 0 <= x ->
  y ^ x mod p = 1 -> (order_mod y p | x).
Proof.
  intros.
  pose proof (order_mod_bounds y p prime_p).
  destruct (Z.eq_dec x 0); [subst; apply Z.divide_0_r|].
  apply pow_mod_order in H0; (omega || auto).
  assert (0 < order_mod y p) by omega.
  apply (Z.mod_pos_bound x _) in H2.
  pose proof (Z.nonpos_pos_cases (x mod order_mod y p)).
  destruct H3. {
    assert (x mod order_mod y p = 0) by omega.
    apply Z.mod_divide; omega.
  } {
    assert (1 <= x mod order_mod y p <= p - 2) by omega.
    pose proof (order_mod_upper_bound _ y p prime_p H4 H0).
    omega.
  }
Qed.

Lemma e_order_order_mod : forall y p (prime_p : prime p) (lt_1_p : 1 < p),
  EGroup.e_order Z.eq_dec y (ZPGroup p lt_1_p) = FGroup.g_order (ZPGroup p lt_1_p)
  -> order_mod y p = p - 1.
Proof.
Admitted.
*)

Lemma in_ZPGroup_range (n : Z) (n_pos : 1 < n) (p : Z) :
  List.In p (FGroup.s (ZPGroup n n_pos)) -> 1 <= p < n.
Proof.
unfold ZPGroup; simpl; intros Hin.
pose proof (IGroup.isupport_incl Z (pmult n) (mkZp n) 1 Z.eq_dec).
unfold List.incl in *.
specialize (H p Hin).
apply in_mkZp in H; auto.
destruct (Z.eq_dec p 0); try subst.
apply IGroup.isupport_is_inv_true in Hin.
rewrite rel_prime_is_inv in Hin by auto.
pose proof (not_rel_prime_0 n n_pos).
destruct (rel_prime_dec 0 n) in Hin; try congruence.
omega.
Qed.

Lemma generator_subgroup_is_group p (lt_1_p : 1 < p): forall y,
  (List.In y (FGroup.s (ZPGroup p lt_1_p))
  /\ EGroup.e_order Z.eq_dec y (ZPGroup p lt_1_p) = FGroup.g_order (ZPGroup p lt_1_p))
  -> forall a, List.In a (FGroup.s (ZPGroup p lt_1_p)) ->
  List.In a (EGroup.support Z.eq_dec y (ZPGroup p lt_1_p)).
Proof.
  intros.
  destruct H as [in_ZPGroup_y y_order].
  pose proof (EGroup.support_incl_G Z Z.eq_dec (pmult p) y (ZPGroup p lt_1_p) in_ZPGroup_y).
  eapply Permutation.permutation_in; [|eauto].
  apply Permutation.permutation_sym.
  eapply UList.ulist_eq_permutation; try apply EGroup.support_ulist; eauto.
  unfold EGroup.e_order, FGroup.g_order in y_order.
  apply Nat2Z.inj in y_order.
  auto.
Qed.

Lemma exists_primitive_root_power : forall p (prime_p : prime p) (lt_1_p : 1 < p)
  (p_odd : p <> 2) (* This is provable for p = 2, but we are lazy. *), 
  (exists y, List.In y (FGroup.s (ZPGroup p lt_1_p))
  /\ EGroup.e_order Z.eq_dec y (ZPGroup p lt_1_p) = FGroup.g_order (ZPGroup p lt_1_p)
  /\ (forall x (x_range : 1 <= x <= p - 1), exists j, 0 <= j <= p - 1 /\ y ^ j mod p = x)).
Proof.
  intros.
  destruct (Zp_cyclic p lt_1_p prime_p) as [y [y_in_ZPGroup y_order]].
  exists y; repeat split; auto.
  intros x x_range.
  pose proof (in_ZPGroup_range p lt_1_p y y_in_ZPGroup) as y_range1.
  assert (0 <= y < p) as y_range0 by omega. 
  pose proof (rel_prime_le_prime y p prime_p y_range1) as rel_prime_y_p.
  pose proof (in_ZPGroup p lt_1_p y rel_prime_y_p y_range0) as in_ZPGroup_y.
  destruct (EGroup.support_gpow Z Z.eq_dec (pmult p) y (ZPGroup p lt_1_p) in_ZPGroup_y x) as [k [k_range gpow_y_k]].
  assert (rel_prime x p) by (apply rel_prime_le_prime; (omega || auto)).
  assert (List.In x (FGroup.s (ZPGroup p lt_1_p))).
  apply in_ZPGroup; (omega || auto).
  apply generator_subgroup_is_group; eauto.
  exists k; split. {
    split; try omega.
    unfold EGroup.e_order in y_order.
    rewrite y_order in k_range.
    rewrite <- phi_is_order in k_range.
    rewrite Euler.prime_phi_n_minus_1 in k_range; (omega || auto).
  }
  assert (y mod p = y) as y_small by (apply Z.mod_small; omega).
  rewrite <- y_small in gpow_y_k.
  rewrite <- (Zpower_mod_is_gpow y k p lt_1_p) in gpow_y_k by (omega || auto).
  auto.
Qed.

Lemma pred_odd : forall x, ~ (2 | x) -> (2 | x - 1).
Proof.
  intros.
  rewrite <- Z.mod_divide in H by omega.
  rewrite <- Z.mod_divide by omega.
  pose proof (Zmod_odd x).
  break_if; intuition.
  replace x with (Z.succ (x - 1)) in Heqb by omega.
  rewrite Z.odd_succ in Heqb.
  pose proof (Zmod_even (x - 1)).
  rewrite Heqb in H1; simpl in H1; auto.
Qed.

Ltac Zdivide_exists_mul := match goal with
| [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H; destruct H
| [ |- (?a | ?b) ] => apply Z.mod_divide; try apply Zmod_divides
end; (omega || auto).

Lemma prime_pred_divide2 : forall p (prime_p : prime p) (p_odd : p <> 2),
  (2 | p - 1).
Proof.
  intros.
  apply pred_odd.
  intuition.
  Zdivide_exists_mul; [ | pose proof (Z.mod_pos_bound p 2); omega].
  rewrite Z.mul_comm in H.
  apply Zdivide_intro in H.
  apply prime_divisors in H; auto.
  intuition.
  prime_bound.
Qed.

Lemma prime_odd : forall p (prime_p : prime p) (p_odd : p <> 2),
  Zodd p.
Proof.
  intros.
  pose proof (prime_pred_divide2 p prime_p p_odd).
  assert (Zeven (p - 1)) by (Zdivide_exists_mul; [rewrite H; apply Zeven_2p
  | pose proof (Zmod_pos_bound (p - 1) 2); omega]).
  replace p with (Z.succ (p - 1)) by ring.
  apply Zodd_Sn; auto.
Qed.

Lemma prime_minus1_div2_exact : forall x p (prime_p : prime p) (p_odd : p <> 2),
  (x * 2 + 1 = p) -> x = (p - 1) / 2.
Proof.
  intros.
  apply Zeq_plus_swap in H.
  replace (p - 1) with (2 * ((p - 1) / 2)) in H by
    (symmetry; apply Z_div_exact_2; try apply Z.mod_divide;
    try apply prime_pred_divide2; (auto || omega)).
  ring_simplify in H.
  apply Z.mul_cancel_l in H; omega.
Qed.

Lemma divide_mul_div: forall a b c, a <> 0 -> c <> 0 ->
  (a | b * (a / c)) -> (c | a) -> (c | b).
Proof.
  intros.
  Zdivide_exists_mul.
  Zdivide_exists_mul.
  rewrite H2 in H1.
  rewrite Z_div_mul' in H1 by auto.
  replace (b * x) with (x * b) in H1 by ring.
  replace (c * x * x0) with (x * (x0 * c)) in H1 by ring.
  rewrite Z.mul_cancel_l in H1 by (intuition; rewrite H3 in H2; ring_simplify in H2; intuition).
  eapply Zdivide_intro; eauto.
Qed.

Ltac ereplace x := match type of x with ?t =>
  let e := fresh "e" in evar (e:t); replace x with e; subst e end.

Lemma euler_criterion : forall (a x p : Z) (prime_p : prime p)
  (p_odd : p <> 2) (a_range : 1 <= a <= p - 1) (x_div2_minus1p : x * 2 + 1 = p)
  (pow_a_x : a ^ x mod p = 1), exists b : Z, b * b mod p = a mod p.
Proof.
  intros.
  assert (1 < p) as lt_1_p by prime_bound.
  destruct (exists_primitive_root_power p prime_p lt_1_p) as [y [in_ZPGroup_y [y_order gpow_y]]]; auto.
  destruct (gpow_y a a_range) as [j [j_range pow_y_j]].
  rewrite mod_pow in pow_a_x by prime_bound.
  replace a with (a mod p) in pow_y_j by (apply Z.mod_small; omega).
  rewrite <- pow_y_j in pow_a_x.
  rewrite <- mod_pow in pow_a_x by prime_bound.
  rewrite <- Z.pow_mul_r in pow_a_x by omega.
  assert (p - 1 | j * x) as divide_mul_j_x. {
    rewrite <- phi_is_order in y_order.
    rewrite Euler.prime_phi_n_minus_1 in y_order by auto.
    ereplace (p-1); try eapply EGroup.e_order_divide_gpow; eauto with zarith.
    simpl.
    apply in_ZPGroup_range in in_ZPGroup_y.
    replace y with (y mod p) by (apply Z.mod_small; omega).
    erewrite <- Zpower_mod_is_gpow; eauto.
    apply rel_prime_le_prime; (omega || auto).
    apply Z.mul_nonneg_nonneg; intuition; omega.
  }
  exists (y ^ (j / 2)).
  rewrite <- Z.pow_add_r by (apply Z.div_pos; omega).
  rewrite <- Z_div_plus by omega.
  rewrite Z.mul_comm.
  rewrite (prime_minus1_div2_exact x p) in divide_mul_j_x; auto.
  apply (divide_mul_div _ j 2) in divide_mul_j_x;
    try (apply prime_pred_divide2 || prime_bound); auto.
  rewrite <- Zdivide_Zdiv_eq by (auto || omega).
  rewrite Zplus_diag_eq_mult_2.
  rewrite Z_div_mult by omega; auto.
Qed.

Lemma divide2_1mod4 : forall x, x mod 4 = 1 -> 0 <= x -> (2 | x / 2).
Proof.
  intros.
  assert (Z.to_nat x mod 4 = 1)%nat. {
    replace 1%Z with (Z.of_nat 1) in H by auto.
    replace (x mod 4)%Z with (Z.of_nat (Z.to_nat x mod 4)) in H
      by (rewrite mod_Zmod by omega; rewrite Z2Nat.id; auto).
    apply Nat2Z.inj in H; auto.
  }
  remember (Z.to_nat x / 4)%nat as c.
  pose proof (divide2_1mod4_nat c (Z.to_nat x) Heqc H1).
  destruct H2.
  replace 2%nat with (Z.to_nat 2) in H2 by auto.
  apply inj_eq in H2.
  rewrite div_Zdiv in H2 by (replace (Z.to_nat 2) with 2%nat by auto; omega).
  rewrite Nat2Z.inj_mul in H2.
  do 2 rewrite Z2Nat.id in H2 by (auto || omega).
  rewrite Z.mul_comm in H2.
  symmetry in H2.
  apply Zdivide_intro in H2; auto.
Qed.

Lemma minus1_even_pow : forall x y, (2 | y) -> (1 < x) -> (0 <= y) -> ((x - 1) ^ y mod x = 1).
Proof.
  intros.
  apply Zdivide_Zdiv_eq in H; try omega.
  rewrite H.
  rewrite Z.pow_mul_r by omega.
  assert ((x - 1)^2 mod x = 1). {
    replace ((x - 1)^2) with (x ^ 2 - 2 * x + 1)
      by (do 2 rewrite Z.pow_2_r; rewrite Z.mul_sub_distr_l; do 2 rewrite Z.mul_sub_distr_r; omega).
    rewrite Zplus_mod.
    rewrite Z.pow_2_r.
    rewrite <- Z.mul_sub_distr_r.
    rewrite Z_mod_mult.
    do 2 rewrite Zmod_1_l by auto; auto.
  }
  rewrite <- (Z2Nat.id (y / 2)) by omega.
  induction (Z.to_nat (y / 2)); try apply Zmod_1_l; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite Zmult_mod.
  rewrite IHn.
  rewrite H2.
  simpl.
  apply Zmod_1_l; auto.
Qed.

Lemma minus1_square_1mod4 : forall (p : Z) (prime_p : prime p),
  (p mod 4 = 1)%Z -> exists b : Z, (b * b mod p = p - 1)%Z.
Proof.
  intros.
  assert (4 <> 0)%Z by omega.
  pose proof (Z.div_mod p 4 H0).
  pose proof (prime_ge_2 p (prime_p)).
  assert (2 | p / 2)%Z by (apply divide2_1mod4; (auto || omega)).
  replace (p - 1) with ((p - 1) mod p) by (apply Zmod_small; omega).
  assert (p <> 2) as neq_p_2 by intuition.
  apply (euler_criterion (p - 1) (p / 2) p prime_p);
    [ auto | omega | | apply minus1_even_pow; (omega || auto); apply Z_div_pos; omega].
  pose proof (prime_odd p prime_p neq_p_2).
  rewrite <- Zdiv2_div.
  rewrite Zodd_div2; (ring || auto).
Qed.
