From Stdlib Require Import ZArith ZModOffset Zdiv Zdivisibility Lia.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.
From Stdlib Require Import Zmod.ZmodDef Zmod.ZstarDef Zmod.Zmod Zmod.Zstar.
Require Import Crypto.Util.ZUtil.Coprime.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Mul.
Require Import Crypto.Util.ListUtil.ListProd.
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ListUtil.Seq.
Require Import Crypto.Util.ZmodUtil.Elements.
Require Import Crypto.Util.ZmodUtil.EulerCriterion.

#[local] Open Scope Z_scope.
#[local] Coercion Z.pos : positive >-> Z.
#[local] Coercion N.pos : positive >-> N.
#[local] Coercion Z.of_N : N >-> Z.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
#[local] Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Zstar.
Import ZmodDef.
Import ZmodDef.Zmod ZmodBase.Zmod Elements.Zmod EulerCriterion.Zmod.
Import ZstarDef.Zstar ZstarBase.Zstar Elements.Zstar EulerCriterion.Zstar.
#[local] Notation "∏ xs" := (prod xs) (at level 40).

#[local] Lemma mul_signed_subgroups_abs (p q : positive) (Hp : p mod 2 = 1) (Hq : q mod 2 = 1) x y :
  abs x = abs y :> Zstar (p*q) -> Z.smodulo x p * Z.smodulo x q = Z.smodulo y p * Z.smodulo y q.
Proof.
  intros []%eq_abs_iff; [congruence|subst y].
  rewrite to_Zmod_opp, to_Z_opp.
  symmetry.
  rewrite <-Z.smod_mod, Z.mod_mod_divide, Z.smod_mod by (exists q; lia).
  rewrite <-(Z.smod_mod _ q), Z.mod_mod_divide, Z.smod_mod by (exists p; lia).
  rewrite <-(Z.smod_idemp_opp _ p), <-(Z.smod_idemp_opp _ q).
  pose proof Z.smod_pos_bound x p ltac:(lia).
  pose proof Z.smod_pos_bound x q ltac:(lia).
  rewrite !(Z.smod_small (- _)); (zify; Z.to_euclidean_division_equations; nia).
Qed.

Lemma square_prod_positives {p : positive} (prime_p : Z.prime p) (odd_p : 3 <= p) :
  pow (∏ positives p) 2 = opp (pow (opp one) ((p - 1) / 2)).
Proof.
  rewrite pow_2_r.
  pose proof prod_elements_prime prime_p as H.
  rewrite elements_by_sign in H by lia.
  rewrite negatives_as_positives_odd in H by auto using Z.prime_odd.
  apply (f_equal opp) in H; rewrite ?opp_opp in H.
  rewrite prod_app, prod_opp, prod_rev, (mul_comm (pow _ _)), mul_assoc, <-mul_opp_r in H.
  rewrite length_rev, length_positives_prime in H by trivial.
  replace (Z.of_nat (N.to_nat (Pos.pred_N p / 2))) with ((p - 1) / 2) in H by lia.
  apply (f_equal (fun x => mul x (inv (opp (pow (opp one) ((p - 1) / 2)))))) in H.
  rewrite Z2Nat.id in H by (Z.div_mod_to_equations; lia).
  rewrite <-?mul_assoc, mul_inv_same_r, mul_1_r in H.
  rewrite mul_1_l, inv_opp, inv_pow_m1 in H; exact H.
Qed.

#[local] Lemma prod_snd_abspairs
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  ∏ map snd (list_prod (elements p) (positives q)) =
  (-1)^((p-1)/2) * (-1)^((q-1)/2*((p-1)/2)) mod q :> Z.
Proof.
  rewrite List.snd_list_prod, prod_concat, map_repeat, prod_repeat.
  rewrite length_elements_prime, Z2Nat.id by (trivial || Z.div_mod_to_equations; lia).
  replace (p-1) with (2 * ((p-1)/2)) at 1; cycle 1.
  { pose proof Z.prime_odd _ prime_p odd_p. (zify; Z.to_euclidean_division_equations; nia). }
  rewrite pow_mul_r, square_prod_positives, <-mul_m1_l, pow_mul_l, <-pow_mul_r by trivial.
  rewrite ?to_Zmod_mul, ?to_Zmod_pow, ?to_Zmod_opp, ?to_Zmod_1.
  rewrite ?to_Z_mul, ?to_Z_pow_nonneg_r, ?to_Z_opp, ?to_Z_1, ?Z.mod_pow_l, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?(Z.mod_small 1);
    trivial; try (Z.to_euclidean_division_equations; nia).
Qed.

#[local] Lemma prod_fst_abspairs
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  ∏ map fst (list_prod (elements p) (positives q)) = (-1)^((q-1)/2) mod p :> Z.
Proof.
  erewrite List.fst_list_prod, prod_flat_map, map_ext, prod_pow, prod_elements_prime; trivial.
  2: { intros. instantiate (1:=((q-1)/2)).
    rewrite prod_repeat, length_positives_prime; trivial; f_equal.
    zify; Z.to_euclidean_division_equations; nia. }
  rewrite to_Zmod_pow, to_Zmod_opp, to_Zmod_1.
  rewrite to_Z_pow_nonneg_r, to_Z_opp, to_Z_1, Z.mod_pow_l, ?(Z.mod_small 1); trivial;
    Z.to_euclidean_division_equations; nia.
Qed.

Local Notation combine p q :=
  (fun xy : Zstar _ * Zstar _ => Zstar.of_Zmod (Zmod.of_Z (p*q)%positive (Z.combinecong p%positive q%positive (fst xy) (snd xy)))).

Lemma prod_combinecong
  {p q : positive} {Hp : 3 <= p} {Hq : 3 <= q} {coprime_p_q : Z.coprime p q} (ps : list (Zstar p * Zstar q)) :
  ∏ (map (combine p q)) ps =
  Zstar.of_Zmod (Zmod.of_Z (p*q) (Z.combinecong p q (∏ map fst ps) (∏ map snd ps))).
Proof.
  induction ps as [|[x y]]; cbn [fst snd map]; rewrite ?prod_nil, ?prod_cons; [|rewrite IHps; clear IHps].
  { erewrite <-Z.combinecong_complete_coprime_nonneg_nonneg with (a:=1);
    repeat (rewrite ?Z.mod_small, ?to_Zmod_1, ?to_Z_1;
      trivial; try (Z.to_euclidean_division_equations; nia)). }
  rewrite ?to_Zmod_mul, ?to_Z_mul.
  symmetry; erewrite <-Z.combinecong_complete_coprime_nonneg_nonneg with
    (a:=(Z.combinecong p q x y) * (Z.combinecong p q (∏ map fst ps) (∏ map snd ps)))
    by (trivial; try lia; rewrite <-Zmult_mod_idemp_r, <-Zmult_mod_idemp_l,
      ?(proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?(proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?Zmult_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmod_mod; trivial).
  rewrite of_Z_mod, of_Z_mul, of_Zmod_mul; trivial;
  rewrite to_Z_of_Z, Z.coprime_mod_l_iff, ?Pos2Z.inj_mul; apply Z.coprime_mul_r;
  rewrite <-Z.coprime_mod_l_iff,
      ?(proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)),
      ?(proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)), ?Z.coprime_mod_l_iff;
  auto using to_Zmod_range.
Qed.

Lemma abs_prod_positives_semiprime
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  abs (∏ positives (p*q)) = abs (∏ map (combine p q) (list_prod (elements p) (positives q))).
Proof.
  intros.
  pose (absq (x : Zstar (p*q)) := if 0 <? Z.smodulo x q then x else opp x).
  assert (abs_absq : forall x, abs (absq x) = abs x). {
    intros. cbv [absq]. destruct Z.ltb; auto using abs_opp. }
  erewrite <-abs_prod_abs, map_ext, <-map_map, abs_prod_abs by (symmetry; apply abs_absq).
  f_equal.
  eapply prod_Permutation .
  eapply Permutation.NoDup_Permutation_bis; cbv [incl].
  { eapply NoDup_map_inv with (f:=abs).
    erewrite map_map, map_ext by (eapply abs_absq).
    pose proof @NoDup_positives (p*q).
    assert (map abs (positives (p * q)) = positives (p*q)).
    { erewrite map_ext_in, map_id; try intros x ?%in_positives; auto using abs_pos. lia. }
    rewrite <-H0 in H; exact H. }
  { rewrite ?length_map, ?length_prod, ?length_elements_prime by trivial.
    pose proof Z.prime_odd p prime_p odd_p as Hp'.
    pose proof Z.prime_odd q prime_q odd_q as Hq'.
    assert (p <> q) by (cbv [Z.coprime] in *; intro; subst; rewrite Z.gcd_diag in *; lia).
    rewrite length_positives_prime, length_positives_odd, length_elements_semiprime by
      (trivial; Z.to_euclidean_division_equations; lia).
    zify. rewrite Nat2Z.inj_div in *. zify. Z.to_euclidean_division_equations. nia. }
  setoid_rewrite in_map_iff.
  intros ? (?&[]&?).
  exists (of_Zmod (of_Z p (absq x)), of_Zmod (of_Z q (absq x))); cbn [fst snd].
  rewrite in_prod_iff, in_positives; [|lia].
  pose proof coprime_to_Zmod x as C; apply Z.coprime_mul_r_iff in C; case C as [].
  pose proof coprime_to_Zmod (absq x) as C;apply Z.coprime_mul_r_iff in C; case C as [].
  repeat rewrite ?to_Zmod_of_Zmod, ?to_Z_of_Z, ?signed_of_Z,
    ?Z.combinecong_mod_l, ?Z.combinecong_mod_r, ?Z.coprime_mod_l_iff; trivial; [].
  (intuition auto using in_elements); [|]; cycle 1. 
  { cbv [absq]; case (Z.ltb_spec 0 (Z.smodulo x q)) as []; trivial. 
    rewrite to_Zmod_opp, to_Z_opp, <-Z.smod_mod, Z.mod_mod_divide, Z.smod_mod, <-Z.smod_idemp_opp by
      (exists p; lia).
    pose proof Z.smod_pos_bound x q ltac:(lia).
    case (Z.eqb_spec (Z.smodulo x q) 0) as [E|].
    { apply (f_equal (fun x => x mod q)) in E; rewrite Z.mod_smod, Zmod_0_l in E.
      rewrite <-Z.coprime_mod_l_iff, E, Z.coprime_0_l_iff in *. lia. }
    rewrite Z.smod_small; try lia.
    pose proof Z.prime_odd q prime_q odd_q as Hq'; Z.to_euclidean_division_equations; nia. }
  erewrite <-Z.combinecong_complete_coprime_nonneg_nonneg by (trivial; lia).
  rewrite of_Z_mod, of_Z_to_Z, of_Zmod_to_Zmod; trivial.
Qed.

Lemma prod_positives_semiprime
  {p q : positive} {prime_p : Z.prime p} {prime_q : Z.prime q} (odd_p : 3 <= p) {odd_q : 3 <= q} {coprime_p_q : Z.coprime p q} :
  Z.smodulo (∏ positives (p*q)) p =  (-1)^((q-1)/2) * Z.smodulo (q^((p-1)/2)) p.
Proof.
  assert (tl_seq : forall start len, tl (seq start len) = seq (S start) (len-1)).
  { destruct len; rewrite ?Nat.sub_1_r; trivial. }
  assert (
    map_add_seq: forall len start shift : nat, map (Nat.add shift) (seq start len) = seq (shift + start) len
    ).
  { clear; induction len; cbn [seq map]; intros; rewrite ?IHlen, ?Nat.add_succ_r; trivial. }
  assert (
    seq_as_0_l : forall len start shift : nat, seq start len = map (Nat.add start) (seq O len)
    ).
  { clear -map_add_seq; intros. rewrite map_add_seq, Nat.add_0_r; trivial. }
  assert (
div_mul_same_r:
  forall {m : positive} (x y z : Zstar m), div (mul y x) (mul z x) = div y z
  ).
  { clear; intros.
    repeat rewrite <-?mul_inv_r, ?inv_mul, ?(mul_comm x), <-?mul_assoc.
    rewrite mul_inv_same_l, mul_1_r; trivial. }

  assert (div_abs1_r : forall m (x y : Zstar m), abs y = one -> div x y = mul x y).
  { clear; intros m x y H.
    rewrite <-abs_1 in H; eapply eq_sym, eq_abs_iff in H; case H as [->| ->];
        rewrite <-?mul_inv_r, ?inv_opp, ?inv_1; trivial. }

  pose proof Z.prime_odd p prime_p odd_p as Hp'.
  pose proof Z.prime_odd q prime_q odd_q as Hq'.
  rewrite Z.coprime_comm in coprime_p_q.

  assert ((p / 2) < p) by (Z.div_mod_to_equations; nia).

  rewrite <-(Z.smod_smod_divide _ (Pos.mul p q)), smod_unsigned by (exists q; lia).

  (* injecting product into [Zmod p] *)
  rewrite <-signed_of_Z, <-(to_Zmod_of_Zmod (of_Z _ _)); cycle 1.
  { rewrite to_Z_of_Z, <-smod_unsigned, <-Z.mod_smod, Z.smod_smod_divide, Z.mod_smod, Z.coprime_mod_l_iff
      by (exists q; lia).
    pose proof coprime_to_Zmod (∏ positives (p * q)) as Hc;
      apply Z.coprime_mul_r_iff in Hc; case Hc as []; trivial. }

  cbv [positives].
  erewrite to_Zmod_prod, map_map, map_ext_in, map_id; cbv beta.
  2: { intros ? [_ E]%filter_In. apply Z.eqb_eq in E.
    rewrite to_Zmod_of_Zmod by assumption; exact eq_refl. }

  rewrite <-(@of_Z_mod p), <-(Z.mod_smod _ p).
  rewrite <-(@smod_unsigned (p*q)), Z.smod_smod_divide, Z.mod_smod by (exists q; lia).
  rewrite <-Zmod.mod_to_Z.
  assert (forall xs, fold_right Zmod.mul Zmod.one xs mod (p*q)%positive = fold_right Z.mul 1 (map to_Z xs) mod (p*q)%positive) as ->.
  { clear -odd_p odd_q. induction xs; cbn [fold_right map]; rewrite ?to_Z_1, ?to_Z_mul, ?Zmod_mod by lia; trivial.
    rewrite <-Z.mul_mod_idemp_r by lia.
    set ((unsigned (fold_right _ _ _) mod _)) in *.
    rewrite IHxs.
    rewrite Z.mul_mod_idemp_r by lia; trivial. }
  rewrite Z.mod_mod_divide, of_Z_mod by (exists q; lia).
  eassert (forall xs, of_Z _ (fold_right Z.mul 1 xs) = fold_right Zmod.mul Zmod.one (map (of_Z _) xs)) as ->.
  { clear. induction xs; cbn [fold_right map]; rewrite ?of_Z_mul, ?IHxs; trivial. }

  rewrite !map_map.
  rewrite of_Zmod_prod, ?map_map; try lia; cycle 1.
  { eapply Forall_map, Forall_forall; intros ? [? E%Z.eqb_eq]%filter_In.
    apply Z.coprime_mul_r_iff in E; case E as [].
    rewrite to_Z_of_Z, Z.coprime_mod_l_iff by (exists q; lia); trivial. }

  (* inclusion-exclusion principle for [Zmod (p * q)] *)
  erewrite filter_ext, <-filter_filter; cbv beta; cycle 1.
  { instantiate (1:=fun x => Z.gcd x p =? 1). instantiate (1:=fun x => Z.gcd x q =? 1).
    intros x. apply eq_true_iff_eq.
    rewrite andb_true_iff, !Z.eqb_eq, and_comm; apply Z.coprime_mul_r_iff. }

  cbv [Zmod.positives].
  rewrite 2 filter_map_swap, ?map_map.
  rewrite prod_map_filter, filter_filter.
  erewrite (filter_ext_in (fun k => andb _ _) (fun k => (Z.of_nat k mod q) =? 0)); cycle 1.
  { intros ? G; apply in_seq in G.
    rewrite (proj2 (Z.ltb_lt _ _)) in G by lia; cbn [Z.b2z] in G.
    eapply eq_true_iff_eq. rewrite andb_true_iff, <-eq_true_not_negb_iff, 3Z.eqb_eq.
    rewrite !to_Z_of_Z, <-!(Z.gcd_mod_l (Z.of_nat a mod (p * q))),
      !Z.mod_mod_divide, !Z.gcd_mod_l by ((exists q + exists p); lia).
    repeat setoid_rewrite (Z.coprime_comm (Z.of_nat a)).
    rewrite !Z.coprime_prime_l_iff by trivial.
    case (Z.BoolSpec_divide q (Z.of_nat a)); intuition idtac;
    rewrite !Z.mod_divide in *; try trivial; try contradiction; try lia.
    case (Z.lcm_least p q (Z.of_nat a)) as [d ?]; trivial.
    cbv [Z.coprime] in coprime_p_q.
    rewrite Z.gcd_comm, Z.gcd_1_lcm_mul, Z.abs_eq in coprime_p_q by lia; rewrite coprime_p_q in *.
    assert (0 < d) by lia. zify; Z.div_mod_to_equations; nia. }

  eassert ( let f := _ in let n := _ in filter f (seq 1 n) = filter f (seq 0 (S n))) as ->.
  { cbn [seq filter]. rewrite to_Z_0. setoid_rewrite Z.gcd_0_l. rewrite (proj2 (Z.eqb_neq _ _)); trivial; lia. }
  rewrite (proj2 (Z.ltb_lt _ _)) by lia; cbn [Z.b2z].
  eassert (S _ = (Pos.to_nat p * Z.to_nat (q / 2) + S (Z.to_nat (p/2)))%nat)
    as -> by (Z.div_mod_to_equations; nia); rewrite Nat.mul_comm.

  (* filtering numerator *)
  erewrite List.filter_ext; cycle 1.
  { intros k. 
    rewrite to_Z_of_Z, <-Z.gcd_mod_l, Z.mod_mod_divide by (exists q; lia).
    exact eq_refl. }

  rewrite seq_app, seq_mul_r, List.flat_map_concat_map.
  repeat rewrite <-?List.concat_filter_map, ?map_app, ?concat_map, ?map_map, ?filter_app.
  cbn [Nat.add].

  erewrite List.map_ext; cycle 1.
  { intros i.
    replace (Pos.to_nat p) with (S (Pos.to_nat p-1)) at 2 by lia.
    cbn [List.seq List.filter].
    rewrite Nat2Z.inj_mul, positive_nat_Z, Z_mod_mult, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)) by lia.
    erewrite filter_ext_in, filter_true; [exact eq_refl|]; intros j ?%in_seq; cbv beta.
    rewrite Z.gcd_mod_l, Z.gcd_comm.
    apply Z.eqb_eq, Z.coprime_prime_l_iff; trivial.
    rewrite <-Z.mod_divide, (Z.mod_diveq (Z.of_nat i)); lia. }

  cbn [List.seq List.filter].
  rewrite Nat2Z.inj_mul, positive_nat_Z, Z_mod_mult, Z.gcd_0_l, (proj2 (Z.eqb_neq _ _)) by lia.
  erewrite filter_ext_in, filter_true; cycle 1. 
  { intros j ?%in_seq; cbv beta.
  rewrite Z.gcd_mod_l, Z.gcd_comm.
    apply Z.eqb_eq, Z.coprime_prime_l_iff; trivial.
  rewrite <-Z.mod_divide, (Z.mod_diveq (Z.of_nat (Z.to_nat (q/2)))); lia. }

  (* multiplying numerator *)
  rewrite prod_app, prod_concat, map_map.
  erewrite map_ext_in, (map_const (opp one)), prod_repeat, length_seq, Z2Nat.id; revgoals.
  { intros i **.
    rewrite <-Nat.add_1_l, Nat.add_comm. rewrite <-map_add_seq, map_map.
    erewrite map_ext_in; cycle 1.
    { intros k Hk; apply in_seq in Hk.
      rewrite to_Z_of_Z, <-of_Z_mod, Z.mod_mod_divide by (exists q; lia).
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z, Z.add_comm.
      rewrite Z.mod_add, of_Z_mod by lia. exact eq_refl. }
    rewrite <-map_map. rewrite <-tl_seq.
    rewrite <-tl_map.
    eassert (map _ _ = Zmod.elements p) as -> by trivial.
      pose proof to_Zmod_elements_prime p ltac:(trivial).
    eassert (map of_Zmod _ = Zstar.elements p) as ->.
    { erewrite <-to_Zmod_elements_prime, map_map, map_ext_in, map_id; trivial; intros.
      rewrite of_Zmod_to_Zmod. trivial. }
    rewrite prod_elements_prime by trivial. exact eq_refl. }
  { clear -odd_q; Z.div_mod_to_equations; nia. }

  erewrite <-Nat.add_1_r, <-map_add_seq, map_map, map_ext_in; cycle 1.
  { intros k **; cbv beta. rapply f_equal.
      rewrite to_Z_of_Z, <-of_Z_mod, Z.mod_mod_divide by (exists q; lia).
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, positive_nat_Z, Z.add_comm, Z2Nat.id by
      (clear -odd_p; Z.div_mod_to_equations; nia).
    rewrite Z.mod_add, of_Z_mod by lia; trivial. }

  (* filtering denominator *)
  eassert (filter _ (seq 1 _) = map (Nat.mul (Z.to_nat q)) (seq 1 (Z.to_nat (p/2)))) as ->.
  { erewrite filter_ext with (g:=fun x => (x mod Pos.to_nat q =? 0 mod Z.to_nat q)%nat); cycle 1.
    { intros i; eapply eq_true_iff_eq.
      rewrite Nat.Div0.mod_0_l.
      rewrite Z.eqb_eq, Nat.eqb_eq, <-Nat2Z.inj_iff, Nat2Z.inj_mod; lia. }
    rewrite filter_cong_seq by lia.
    rewrite Nat.Div0.mod_0_l, Nat.add_0_l, !(Nat.mod_small 1), !(Nat.div_small 1) by lia.
    assert (2 * (Z.to_nat ((Z.abs (p * q) - 1) / 2) mod Z.to_nat q) <= Z.to_nat q)%nat.
    { repeat rewrite ?Nat2Z.inj_le, ?Nat2Z.inj_mod, ?Nat2Z.inj_mul by lia.
      rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia. }
    erewrite filter_ext_in, filter_false; cycle 1; cbn [List.app].
    { intros i ?%in_seq; apply Nat.eqb_neq; intros [d X]%Nat.Lcm0.mod_divide.
      subst i; destruct d; try nia. }
    rewrite map_ext_in with (g:=Nat.add (Z.to_nat q)), map_map; cycle 1.
    { intros iq [i [? Hi%in_seq]]%in_map_iff; subst iq.
      repeat rewrite <-?Nat2Z.inj_iff, ?Z2Nat.id, ?Nat2Z.inj_mod, ?Nat2Z.inj_div, ?Nat2Z.inj_add, ?Nat2Z.inj_sub, ?Nat2Z.inj_mul; [|(zify; Z.to_euclidean_division_equations; nia)..].
      rewrite Zminus_mod_idemp_r.
      rewrite <-Z.mod_add with (a:=Z.sub _ _) (b:=-2%Z) by lia.
      eassert (_+-2*q = - (1 + (Z.abs (p*q)-1)/2)) as -> by lia.
      rewrite Z_mod_nz_opp_full by
        (rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia).
      enough ((1 + (Z.abs (p * q) - 1) / 2) mod q = 1 + ((Z.abs (p * q) - 1) / 2) mod q) by lia.
      rewrite <-Z.add_mod_idemp_r by lia. rewrite Z.mod_small; trivial.
      rewrite (Z.mod_diveq (p/2)); zify; Z.to_euclidean_division_equations; nia.
    }
    rewrite map_ext with (g:=fun i => Nat.mul (Z.to_nat q) (S i)), <-map_map, seq_shift by nia.
    f_equal. f_equal. repeat rewrite <-?Nat2Z.inj_iff, ?Z2Nat.id, ?Nat2Z.inj_div;
      zify; Z.to_euclidean_division_equations; nia. }

  (* multiplying denominator *)
  erewrite map_map, (map_ext_in (fun x : nat => of_Zmod (of_Z p (to_Z _)))); cycle 1.
  { intros ? L%in_seq.
    rewrite to_Z_of_Z, <-of_Z_mod, Z.mod_mod_divide by (exists q; lia).
    rewrite Nat2Z.inj_mul, Z2Nat.id, of_Z_mod, of_Z_mul by lia.
    rewrite of_Zmod_mul; cycle 1.
    { rewrite to_Z_of_Z,  Z.coprime_mod_l_iff; trivial. }
    { rewrite to_Z_of_Z,  Z.coprime_mod_l_iff, Z.coprime_comm.
      apply Z.coprime_prime_small; trivial; lia. }
    exact eq_refl. }
  rewrite <-map_map with (g := mul _), prod_map_mul, length_map, length_seq.

  (* cancellation *)
  rewrite div_mul_same_r, Z2Nat.id by (zify; Z.div_mod_to_equations; lia).
  eassert ((p / 2) = (p-1)/2) as -> by (zify; Z.div_mod_to_equations; lia).
  eassert ((q / 2) = (q-1)/2) as -> by (zify; Z.div_mod_to_equations; lia).
  rewrite div_abs1_r by (rewrite euler_criterion_existsb, abs_of_bool; trivial).

  pose proof (@euler_criterion_existsb p (of_Zmod (of_Z _ q)) ltac:(trivial)) as Heul.
  apply to_Zmod_inj_iff, signed_inj_iff in Heul; revert Heul.

  (* zification *)
  rewrite ?to_Zmod_mul, ?to_Zmod_pow, ?to_Zmod_opp, ?to_Zmod_1.
  rewrite signed_mul, ?signed_pow_nonneg_r, ?signed_opp_small, ?signed_1 by
    (rewrite ?signed_1; zify; Z.div_mod_to_equations; lia).
  rewrite to_Zmod_of_Zmod by (rewrite to_Z_of_Z, Z.coprime_mod_l_iff; trivial).
  rewrite signed_of_Z, Z.smod_pow_l.
  intro Heul.
  rewrite 2Z.smod_small; trivial.

  all : clear -Heul odd_p odd_q Hp' Hq'; rewrite ?Z.pow_m1_l; repeat (case Z.odd; [|]);
     try solve [simpl Z.mul; rewrite ?(Z.gcd_opp_l 1), Z.gcd_1_l; trivial];
     try (zify; Z.to_euclidean_division_equations; nia).
  all : destruct existsb in *; rewrite ?signed_true, ?signed_false in * by lia.
  all : rewrite Heul; clear Heul.
  all : rewrite Z.smod_small; try (zify; Z.to_euclidean_division_equations; nia).
Qed.

Lemma quadratic_reciprocity'
  (p q : positive) (prime_p : Z.prime p) (prime_q : Z.prime q) (odd_p : 3 <= p) (odd_q : 3 <= q) (coprime_p_q : Z.gcd p q = 1) :
  Z.smodulo (q ^ ((p - 1) / 2)) p * Z.smodulo (p ^ ((q - 1) / 2)) q =
  (-1) ^ ((q - 1) / 2 * ((p - 1) / 2)).
Proof.
  pose proof Z.prime_odd p prime_p odd_p as Hp'.
  pose proof Z.prime_odd q prime_q odd_q as Hq'.

  unshelve epose proof abs_prod_positives_semiprime(p:=p)(q:=q) _ as H; trivial.
  unshelve erewrite prod_combinecong, prod_snd_abspairs, prod_fst_abspairs in H; trivial.
  progress rewrite ?Z.combinecong_mod_l, ?Z.combinecong_mod_r in H.
  apply mul_signed_subgroups_abs, eq_sym in H; trivial.
  progress replace (Z.smodulo (∏ positives (p*q)) q) with (Z.smodulo (∏ positives (q*p)) q) in H
    by (rewrite Z.mul_comm; trivial).
  erewrite 2@prod_positives_semiprime in H by (trivial || rewrite Z.coprime_comm; trivial).

  rewrite !to_Zmod_of_Zmod, !to_Z_of_Z in H.
  2: rewrite to_Z_of_Z, Z.coprime_mod_l_iff; apply Z.coprime_mul_r_iff;
    split; rewrite <-Z.coprime_mod_l_iff;
    rewrite (proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q))
    || rewrite (proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)); rewrite Z.coprime_mod_l_iff.
  rewrite <-(Z.smod_mod _ p), Z.mod_mod_divide,
    (proj1 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)), Z.smod_mod in H by (exists q; lia).
  rewrite <-(Z.smod_mod _ q), Z.mod_mod_divide,
    (proj2 (Z.combinecong_sound_coprime _ _ _ _ coprime_p_q)), Z.smod_mod in H by (exists p; lia).

  rewrite ?(Z.smod_small ((-1)^_)), ?(Z.smod_small ((-1)^_*(-1)^_)) in H.
  enough ((-1) ^ ((p - 1) / 2) * (-1) ^ ((q - 1) / 2) <> 0) by nia.
  all : clear -odd_p odd_q Hp' Hq'; rewrite ?Z.pow_m1_l; repeat (case Z.odd; [|]);
     try solve [simpl Z.mul; rewrite ?(Z.coprime_opp_l 1); trivial using Z.coprime_1_l];
     try (zify; Z.to_euclidean_division_equations; nia).
Qed.

End Zstar.
