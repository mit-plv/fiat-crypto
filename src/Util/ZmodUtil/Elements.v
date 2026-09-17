From Stdlib Require Import ZArith ZModOffset Zdiv Zdivisibility Lia.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.
From Stdlib Require Import Zmod.ZmodDef Zmod.ZstarDef Zmod.Zmod Zmod.Zstar.
Require Import Crypto.Util.ZUtil.Coprime.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ListUtil.ListProd.
Require Import Crypto.Util.ListUtil.Permutation.

#[local] Open Scope Z_scope.
#[local] Coercion Z.pos : positive >-> Z.
#[local] Coercion N.pos : positive >-> N.
#[local] Coercion Z.of_N : N >-> Z.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
#[local] Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Zmod.
Import ZmodDef.Zmod ZmodBase.Zmod.
Lemma elements_mul_coprime (a b : positive) (H : Z.coprime a b) :
  Permutation (elements (a * b))
    (map (fun xy : Zmod _ * Zmod _ => Zmod.of_Z (a*b) (Z.combinecong a b (fst xy) (snd xy)))
      (list_prod (elements a) (elements b))).
Proof.
  eapply NoDup_Permutation_bis; try apply NoDup_elements; rewrite ?length_map, ?length_prod, ?length_elements; try lia.
  intros xy G; rewrite in_map_iff; exists (of_Z _ xy, of_Z _ xy); cbn [fst snd].
  split; cycle 1. { apply List.in_prod; apply in_elements; lia. }
  apply to_Z_inj; rewrite !to_Z_of_Z, Z.combinecong_mod_l, Z.combinecong_mod_r.
  symmetry; rewrite <-2mod_to_Z at 1; f_equal.
  apply Z.combinecong_complete_coprime_nonneg_nonneg; trivial; lia.
Qed.
End Zmod.

Module Zstar.
Import ZmodDef.Zmod ZmodBase.Zmod ZstarDef.Zstar ZstarBase.Zstar.

Lemma elements_mul_coprime (a b : positive) (H : Z.coprime a b) :
  Permutation (elements (a * b))
    (map (fun xy : Zstar _ * Zstar _ => of_Zmod (Zmod.of_Z (a*b) (Z.combinecong a b (fst xy) (snd xy))))
      (list_prod (elements a) (elements b))).
Proof.
  pose proof Zmod.elements_mul_coprime a b H as P.
  eapply (Permutation_filter (fun x : Zmod (a*b) => Z.gcd x (a*b) =? 1)) in P.
  eapply (Permutation_map (@of_Zmod (a*b))) in P.
  rewrite <-Pos2Z.inj_mul in P; rewrite P; clear P.
  symmetry; rewrite <-map_map with (g:=of_Zmod), filter_map_swap; Morphisms.f_equiv.
  erewrite <-map_ext, <-map_map with (f := fun xy : Zstar _ * Zstar _ => (fst xy : Zmod _, snd xy : Zmod _)); [ eapply f_equal | intros; exact eq_refl ].
  cbv [elements].
  do 2 (case Z.eqb_spec; try lia); intros.
  erewrite list_prod_map_map, map_map, list_prod_filter_filter;
  erewrite map_ext_in, map_id, filter_ext; trivial; intros [x y]; cbn [fst snd].
  { case (Z.combinecong_sound_coprime a b x y ltac:(trivial)) as [Hx Hy].
    apply eq_true_iff_eq; rewrite andb_true_iff, !Z.eqb_eq.
    rewrite Zmod.to_Z_of_Z, Pos2Z.inj_mul.
    setoid_rewrite Z.coprime_mul_r_iff.
    rewrite <-(Z.coprime_mod_l_iff _ a), <-(Z.coprime_mod_l_iff _ b).
    rewrite Z.mod_prod_mod_factor_l, Z.mod_prod_mod_factor_r, Hx, Hy.
    rewrite Z.coprime_mod_l_iff, Z.coprime_mod_l_iff. reflexivity. }
  { intros [?[?%Z.eqb_eq ?%Z.eqb_eq]%andb_true_iff]%filter_In.
    rewrite !to_Zmod_of_Zmod; trivial. }
Qed.

Lemma length_elements_mul_coprime (a b : positive) (H : Z.coprime a b) :
  length (elements (a*b)) = (length (elements a) * length (elements b))%nat.
Proof. erewrite elements_mul_coprime, ?length_map, ?length_prod; trivial; lia. Qed.

Lemma length_elements_semiprime (p q : positive)
  (Hp : Z.prime p) (Hq : Z.prime q) (H : p <> q) :
  length (elements (p*q)) = Z.to_nat ((p-1)*(q-1)).
Proof.
  rewrite length_elements_mul_coprime, 2length_elements_prime;
    try apply Z.coprime_prime_prime; trivial; nia.
Qed.

Lemma square_roots_opp_prime {p : positive} (Hp : Z.prime p) (x y : Zstar p) :
  pow x 2 = pow y 2 <-> (x = y \/ x = opp y).
Proof.
  rewrite <-3 to_Zmod_inj_iff, 2to_Zmod_pow, to_Zmod_opp.
  rewrite (Zmod.square_roots_opp_prime Hp); reflexivity.
Qed.

Lemma square_roots_1_prime (p : positive) (Hp : Z.prime p) (x : Zstar p) :
  pow x 2 = one <-> (x = one \/ x = opp one).
Proof.
  rewrite <-3to_Zmod_inj_iff, to_Zmod_pow, to_Zmod_opp, to_Zmod_1.
  rewrite (Zmod.square_roots_1_prime Hp); reflexivity.
Qed.

#[local] Notation "∏ xs" := (prod xs) (at level 40).

Definition of_bool m (b : bool) : Zstar m := if b then one else opp one.
Lemma of_bool_negb m b : of_bool m (negb b) = opp (of_bool m b).
Proof. case b; cbn [of_bool negb]; rewrite ?opp_opp; trivial. Qed.
Lemma of_bool_1_iff (m : positive) b : of_bool m b = one <-> b = true \/ m <= 2.
Proof.
  pose proof @opp_1_neq_1 m.
  pose proof @wlog_eq_Zstar_3_pos m one (opp one) ltac:(lia).
  case (Z.leb_spec 3 m); case b; cbn [of_bool]; intuition (congruence || lia).
Qed.
Lemma of_bool_m1_iff (m : positive) b : of_bool m b = (opp one) <-> b = false \/ m <= 2.
Proof.
  pose proof @opp_1_neq_1 m.
  pose proof @wlog_eq_Zstar_3_pos m one (opp one) ltac:(lia).
  case (Z.leb_spec 3 m); case b; cbn [of_bool]; intuition (congruence || lia).
Qed.
Lemma of_bool_1_iff_ge3 m b (Hm : Pos.le 3 m) : of_bool m b = one <-> b = true.
Proof. rewrite of_bool_1_iff; intuition (congruence || lia). Qed.
Lemma of_bool_m1_iff_ge3 m b (Hm : Pos.le 3 m) : of_bool m b = opp one <-> b = false.
Proof. rewrite of_bool_m1_iff; intuition (congruence || lia). Qed.

Lemma abs_of_bool m b : abs (of_bool m b) = one.
Proof. cbv [of_bool]; case b; rewrite ?abs_opp, ?abs_1; trivial. Qed.
Lemma inv_of_bool m b : inv (of_bool m b) = of_bool m b.
Proof. cbv [of_bool]; case b; rewrite ?inv_opp, ?inv_1; trivial. Qed.

Lemma to_Z_true {m : positive} (H : 2 <= m) : Zmod.to_Z (of_bool m true) = 1.
Proof. cbv [of_bool]. rewrite to_Zmod_1, Zmod.to_Z_1, Z.mod_small; lia. Qed.

Lemma to_Z_false {m : positive} : Zmod.to_Z (of_bool m false) = m-1.
Proof.
  case (Pos.eq_dec m 1) as [->|]; trivial.
  case (Pos.eq_dec m 2) as [->|]; trivial.
  cbv [of_bool].
  rewrite to_Zmod_opp, Zmod.to_Z_opp, to_Zmod_1, Zmod.to_Z_1, (Z.mod_diveq (-1));
    rewrite ?(Z.mod_small 1); try lia.
Qed.

Lemma signed_true {m : positive} (H : 3 <= m) : Zmod.signed (of_bool m true) = 1.
Proof. cbv [of_bool]. rewrite to_Zmod_1, Zmod.signed_1; trivial. Qed.

Lemma signed_false {m : positive} (H : 2 <= m) : Zmod.signed (of_bool m false) = -1.
Proof.
  case (Pos.eq_dec m 2) as [->|]; trivial. cbv [of_bool].
  rewrite to_Zmod_opp, Zmod.signed_opp, to_Zmod_1, Zmod.signed_1 by lia.
  rewrite Z.smod_small; trivial. zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma prod_map_filter {A} {m} (f : A -> Zstar m) g (xs : list A) :
  ∏ map f (filter g xs) = div (∏ map f xs) (∏ map f (filter (fun x => negb (g x)) xs)).
Proof.
  induction xs; cbn [map filter]; rewrite ?prod_nil, ?prod_cons, ?div_same; trivial.
  case g; cbn [negb map]; rewrite ?prod_cons, !IHxs, ?div_mul_l; trivial.
  rewrite <-!mul_inv_r, ?inv_mul, ?mul_assoc, ?(mul_comm (f a)), ?mul_assoc; f_equal.
  rewrite <-?mul_assoc, mul_inv_same_r, mul_1_r; trivial.
Qed.

Lemma to_Zmod_prod {m} xs : @to_Zmod m (∏ xs) = fold_right Zmod.mul Zmod.one (map to_Zmod xs).
Proof. induction xs; cbn [map fold_right]; rewrite ?prod_nil, ?prod_cons, ?to_Zmod_1, ?to_Zmod_mul, ?IHxs; auto. Qed.

Lemma of_Zmod_prod {m} xs (Hm : 0 < m) : Forall (fun x : Zmod m => Z.coprime x m) xs -> @of_Zmod m (fold_right Zmod.mul Zmod.one xs) = ∏ (map of_Zmod xs).
Proof.
  intros H. apply wlog_eq_Zstar_3_pos; trivial; intro Hm'.
  induction H; cbn [fold_right map]; rewrite ?prod_nil, ?prod_cons, ?of_Zmod_1, ?of_Zmod_mul, ?IHForall; auto.
  clear H IHForall x; induction H0; cbn [fold_right];
    rewrite ?to_Z_1, ?to_Z_mul, ?Z.coprime_mod_l_iff, ?Z.coprime_mul_l_iff;
    auto using Z.coprime_1_l.
Qed.

Lemma abs_prod_abs m xs : @abs m (∏ map abs xs) = abs (∏ xs).
Proof.
  induction xs; cbn [map]; rewrite ?prod_nil, ?prod_cons; trivial.
  rewrite <-abs_mul_abs_r, IHxs, abs_mul_abs_abs; trivial.
Qed.
End Zstar.
