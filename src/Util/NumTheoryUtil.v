Require Import Coq.ZArith.Zpower Coq.ZArith.Znumtheory Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil.
Require Import Coqprime.Zp.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z.

(* TODO: move somewhere else for lemmas about Coqprime? *)
Lemma in_ZPGroup_range (n : Z) (n_pos : 1 < n) (p : Z) :
  List.In p (FGroup.s (ZPGroup n n_pos)) -> 1 <= p < n.
Proof.
unfold ZPGroup; simpl; intros Hin.
pose proof (IGroup.isupport_incl Z (pmult n) (mkZp n) 1 Z.eq_dec) as H.
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
  intros y H a H0.
  destruct H as [in_ZPGroup_y y_order].
  pose proof (EGroup.support_incl_G Z Z.eq_dec (pmult p) y (ZPGroup p lt_1_p) in_ZPGroup_y).
  eapply Permutation.permutation_in; [|eauto].
  apply Permutation.permutation_sym.
  eapply UList.ulist_eq_permutation; try apply EGroup.support_ulist; eauto.
  unfold EGroup.e_order, FGroup.g_order in y_order.
  apply Nat2Z.inj in y_order.
  auto.
Qed.

Section EulerCriterion.

Variable x p : Z.
Hypothesis prime_p : prime p.
Hypothesis neq_p_2 : p <> 2. (* Euler's Criterion is also provable with p = 2, but we do not need it and are lazy.*)
Hypothesis x_id : x * 2 + 1 = p.

Lemma lt_1_p : 1 < p. Proof using prime_p. prime_bound. Qed.
Lemma x_pos: 0 < x. Proof using prime_p x_id. prime_bound. Qed.
Lemma x_nonneg: 0 <= x. Proof using prime_p x_id. prime_bound. Qed.

Lemma x_id_inv : x = (p - 1) / 2.
Proof using x_id.
  intros; apply Zeq_plus_swap in x_id.
  replace (p - 1) with (2 * ((p - 1) / 2)) in x_id by
    (symmetry; apply Z_div_exact_2; [omega | rewrite <- x_id; apply Z_mod_mult]).
  ring_simplify in x_id; apply Z.mul_cancel_l in x_id; omega.
Qed.

Lemma mod_p_order : FGroup.g_order (ZPGroup p lt_1_p) = p - 1.
Proof using Type.
  intros; rewrite <- phi_is_order.
  apply Euler.prime_phi_n_minus_1; auto.
Qed.

Lemma p_odd : Z.odd p = true.
Proof using neq_p_2 prime_p.
  pose proof (Z.prime_odd_or_2 p prime_p) as H.
  destruct H; auto.
Qed.

Lemma prime_pred_even : Z.even (p - 1) = true.
Proof using neq_p_2 prime_p.
  intros.
  rewrite <- Z.odd_succ.
  replace (Z.succ (p - 1)) with p by ring.
  apply p_odd.
Qed.

Lemma fermat_little: forall a (a_nonzero : a mod p <> 0),
  a ^ (p - 1) mod p = 1.
Proof using prime_p.
  intros a a_nonzero.
  assert (rel_prime a p). {
    apply rel_prime_mod_rev; try prime_bound.
    assert (0 < p) as p_pos by prime_bound.
    apply rel_prime_le_prime; auto; pose proof (Z.mod_pos_bound a p p_pos).
    omega.
  }
  rewrite (Zpower_mod_is_gpow _ _ _ lt_1_p) by (auto || prime_bound).
  rewrite <- mod_p_order.
  apply EGroup.fermat_gen; try apply Z.eq_dec.
  apply in_mod_ZPGroup; auto.
Qed.

Lemma fermat_inv : forall a, a mod p <> 0 -> ((a^(p-2) mod p) * a) mod p = 1.
Proof using prime_p.
  intros a H.
  pose proof (prime_ge_2 _ prime_p).
  rewrite Zmult_mod_idemp_l.
  replace (a ^ (p - 2) * a) with (a^(p-1)).
    2:replace (a ^ (p - 2) * a) with (a^1 * a ^ (p - 2)) by ring.
    2:rewrite <-Zpower_exp; try f_equal; omega.
  auto using fermat_little.
Qed.

Lemma squared_fermat_little: forall a (a_nonzero : a mod p <> 0),
  (a * a) ^ x mod p = 1.
Proof using prime_p x_id.
  intros.
  rewrite <- Z.pow_2_r.
  rewrite <- Z.pow_mul_r by (apply x_nonneg || omega).
  replace (2 * x) with (x * 2 + 1 - 1) by omega.
  rewrite x_id.
  apply fermat_little; auto.
Qed.

Lemma euler_criterion_square_reverse : forall a (a_nonzero : a mod p <> 0),
  (exists b, b * b mod p = a) -> (a ^ x mod p = 1).
Proof using Type*.
  intros a a_nonzero a_square.
  destruct a_square as [b a_square].
  assert (b mod p <> 0) as b_nonzero. {
    intuition.
    rewrite <- Z.pow_2_r in a_square.
    rewrite Z.mod_exp_0 in a_square by prime_bound.
    rewrite <- a_square in a_nonzero.
    auto.
  }
  pose proof (squared_fermat_little b b_nonzero).
  rewrite Z.mod_pow in * by prime_bound.
  rewrite <- a_square.
  rewrite Z.mod_mod; prime_bound.
Qed.

Lemma exists_primitive_root_power :
  (exists y, List.In y (FGroup.s (ZPGroup p lt_1_p))
  /\ EGroup.e_order Z.eq_dec y (ZPGroup p lt_1_p) = FGroup.g_order (ZPGroup p lt_1_p)
  /\ (forall a (a_range : 1 <= a <= p - 1), exists j, 0 <= j <= p - 1 /\ y ^ j mod p = a)).
Proof using Type.
  intros.
  destruct (Zp_cyclic p lt_1_p prime_p) as [y [y_in_ZPGroup y_order]].
  exists y; repeat split; auto.
  intros.
  pose proof (in_ZPGroup_range p lt_1_p y y_in_ZPGroup) as y_range1.
  assert (0 <= y < p) as y_range0 by omega.
  assert (rel_prime y p) as rel_prime_y_p by (apply rel_prime_le_prime; omega || auto).
  assert (rel_prime a p) as rel_prime_a_p by (apply rel_prime_le_prime; omega || auto).
  assert (List.In a (FGroup.s (ZPGroup p lt_1_p))) as a_in_ZPGroup by (apply in_ZPGroup; omega || auto).
  destruct (EGroup.support_gpow Z Z.eq_dec (pmult p) y (ZPGroup p lt_1_p) y_in_ZPGroup a)
    as [k [k_range gpow_y_k]]; [apply generator_subgroup_is_group; auto |].
  exists k; split. {
    unfold EGroup.e_order in y_order.
    rewrite y_order in k_range.
    rewrite mod_p_order in k_range.
    omega.
  } {
    assert (y mod p = y) as y_small by (apply Z.mod_small; omega).
    rewrite <- y_small in gpow_y_k.
    rewrite <- (Zpower_mod_is_gpow y k p lt_1_p) in gpow_y_k by (omega || auto).
    auto.
  }
Qed.

Ltac ereplace x := match type of x with ?t =>
  let e := fresh "e" in evar (e:t); replace x with e; subst e end.

Lemma euler_criterion_square : forall a (a_range : 1 <= a <= p - 1)
  (pow_a_x : a ^ x mod p = 1), exists b, b * b mod p = a.
Proof using Type*.
  intros a a_range pow_a_x.
  destruct (exists_primitive_root_power) as [y [in_ZPGroup_y [y_order gpow_y]]]; auto.
  destruct (gpow_y a a_range) as [j [j_range pow_y_j]]; clear gpow_y.
  rewrite Z.mod_pow in pow_a_x by prime_bound.
  replace a with (a mod p) in pow_y_j by (apply Z.mod_small; omega).
  rewrite <- pow_y_j in pow_a_x.
  rewrite <- Z.mod_pow in pow_a_x by prime_bound.
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
  rewrite x_id_inv in divide_mul_j_x; auto.
  apply (Z.divide_mul_div _ j 2) in divide_mul_j_x;
    try (apply prime_pred_divide2 || prime_bound); auto.
  rewrite <- Zdivide_Zdiv_eq by (auto || omega).
  rewrite Zplus_diag_eq_mult_2.
  replace (a mod p) with a in pow_y_j by (symmetry; apply Z.mod_small; omega).
  rewrite Z_div_mult by omega; auto.
  apply Z.divide2_even_iff.
  apply prime_pred_even.
Qed.

Lemma euler_criterion : forall a (a_range : 1 <= a <= p - 1),
  (a ^ x mod p = 1) <-> exists b, b * b mod p = a.
Proof using Type*.
  intros a a_range; split. {
    exact (euler_criterion_square _ a_range).
  } {
    apply euler_criterion_square_reverse; auto.
    replace (a mod p) with a by (symmetry; apply Zmod_small; omega).
    omega.
  }
Qed.

Lemma euler_criterion_nonsquare : forall a (a_range : 1 <= a <= p - 1),
  (a ^ x mod p <> 1) <-> ~ (exists b, b * b mod p = a).
Proof using Type*.
  intros a a_range; split; intros A B; apply (euler_criterion a a_range) in B; congruence.
Qed.

End EulerCriterion.

Lemma divide2_1mod4 : forall x (x_1mod4 : x mod 4 = 1) (x_nonneg : 0 <= x), (2 | x / 2).
Proof.
  intros x x_1mod4 x_nonneg0.
  assert (Z.to_nat x mod 4 = 1)%nat as x_1mod4_nat. {
    replace 1 with (Z.of_nat 1) in * by auto.
    replace (x mod 4) with (Z.of_nat (Z.to_nat x mod 4)) in *
      by (rewrite mod_Zmod by omega; rewrite Z2Nat.id; auto).
    apply Nat2Z.inj in x_1mod4; auto.
  }
  remember (Z.to_nat x / 4)%nat as c eqn:Heqc.
  destruct (divide2_1mod4_nat c (Z.to_nat x) Heqc x_1mod4_nat) as [k k_id].
  replace 2%nat with (Z.to_nat 2) in * by auto.
  apply inj_eq in k_id.
  rewrite div_Zdiv in k_id by (replace (Z.to_nat 2) with 2%nat by auto; omega).
  rewrite Nat2Z.inj_mul in k_id.
  do 2 rewrite Z2Nat.id in k_id by omega.
  rewrite Z.mul_comm in k_id.
  symmetry in k_id.
  apply Zdivide_intro in k_id; auto.
Qed.

Lemma minus1_even_pow : forall x y, (2 | y) -> (1 < x) -> (0 <= y) -> ((x - 1) ^ y mod x = 1).
Proof.
  intros x y divide_2_y lt_1_x y_nonneg.
  apply Zdivide_Zdiv_eq in divide_2_y; try omega.
  rewrite divide_2_y.
  rewrite Z.pow_mul_r by omega.
  assert ((x - 1) ^ 2 mod x = 1) as square_case. {
    replace ((x - 1) ^ 2) with (x ^ 2 - 2 * x + 1)
      by (do 2 rewrite Z.pow_2_r; rewrite Z.mul_sub_distr_l; do 2 rewrite Z.mul_sub_distr_r; omega).
    rewrite Zplus_mod.
    rewrite Z.pow_2_r.
    rewrite <- Z.mul_sub_distr_r.
    rewrite Z_mod_mult.
    do 2 rewrite Zmod_1_l by auto; auto.
  }
  rewrite <- (Z2Nat.id (y / 2)) by omega.
  induction (Z.to_nat (y / 2)) as [|n IHn]; try apply Zmod_1_l; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite Zmult_mod.
  rewrite IHn.
  rewrite square_case.
  simpl; apply Zmod_1_l; auto.
Qed.

Lemma prime_1mod4_neq2 : forall p (prime_p : prime p), (p mod 4 = 1) -> p <> 2.
Proof.
  intros; intuition.
  assert (4 <> 0)%Z as neq_4_0 by omega.
  pose proof (Z.div_mod p 4 neq_4_0).
  omega.
Qed.

Lemma div2_p_1mod4 : forall (p : Z) (prime_p : prime p) (neq_p_2: p <> 2),
  (p / 2) * 2 + 1 = p.
Proof.
  intros p prime_p neq_p_2.
  destruct (Z.prime_odd_or_2 p prime_p); intuition.
  rewrite <- Zdiv2_div.
  pose proof (Zdiv2_odd_eqn p); break_match; break_match_hyps; congruence || omega.
Qed.

Lemma minus1_square_1mod4 : forall (p : Z) (prime_p : prime p),
  (p mod 4 = 1)%Z -> exists b : Z, (b * b mod p = p - 1)%Z.
Proof.
  intros p prime_p H.
  assert (p <> 2) as neq_p_2 by (apply prime_1mod4_neq2; auto).
  apply (euler_criterion (p / 2) p prime_p).
  + auto.
  + apply div2_p_1mod4; auto.
  + prime_bound.
  + apply minus1_even_pow; [apply divide2_1mod4 | | apply Z_div_pos]; prime_bound.
Qed.


Lemma odd_as_div a : Z.odd a = true -> a = (2*(a/2) + 1)%Z.
Proof.
  rewrite Zodd_mod, <-Zeq_is_eq_bool; intro H_1; rewrite <-H_1.
  apply Z_div_mod_eq; reflexivity.
Qed.
