From Stdlib Require Import ZArith ZModOffset Zdiv Zdivisibility Lia.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.
From Stdlib Require Import Zmod.ZmodDef Zmod.ZstarDef Zmod.Zmod Zmod.Zstar.
Require Import Crypto.Util.ZUtil.Coprime.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ListUtil.ListProd.
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ZmodUtil.Elements.

#[local] Lemma andb_implied_r a b : (a = true -> b = true) -> a && b = a.
Proof. case a, b; trivial. intros H. case H; trivial. Qed.

#[local] Open Scope Z_scope.
#[local] Coercion Z.pos : positive >-> Z.
#[local] Coercion N.pos : positive >-> N.
#[local] Coercion Z.of_N : N >-> Z.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
#[local] Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Module Zstar.
Import ZstarDef.Zstar ZstarBase.Zstar Elements.Zstar.

#[local] Notation "∏ xs" := (prod xs) (at level 40).

Local Infix "*" := mul.
Local Infix "/" := div.

(* TODO: move? Local? *)

#[local] Lemma euler_criterion_subproof  {p : positive} (Hp : Z.prime p) (a : Zstar p) :
  ∏ elements p =
  of_bool _ (negb (existsb (fun x => eqb (pow x 2) a) (elements p))) * pow a ((p-1)/2).
Proof.
  apply wlog_eq_Zstar_3_pos; try lia; intro Hp'.

  (* Tripartite categorization *)
  rewrite existsb_as_filter, negb_involutive.
  set (roots := filter (fun x : Zstar p => eqb (pow x 2) a) (elements p)).
  set (smalls := filter (fun x : Zstar p => x <? div a x) (elements p)).
  set (larges := filter (fun x : Zstar p => div a x <? x) (elements p)).
  assert (HP : Permutation (elements p) (roots ++ (smalls ++ larges))). {
   erewrite (Permutation_partition _ (fun x : Zstar _ => pow x 2 =? a)).
   erewrite (Permutation_partition (snd _) (fun x : Zstar _ => x <? div a x)).
   rewrite !partition_as_filter; cbn [fst snd]; rewrite !filter_filter.
   assert (Hiff : forall x, x*x = a :> Z <-> a/x = x :> Z).
   { intros x; rewrite !Zmod.to_Z_inj_iff, !to_Zmod_inj_iff.
     erewrite <-(mul_cancel_l_iff x _ x), mul_div_r_same_r. split; congruence. }
   erewrite (filter_ext (fun _ => _ && _) (fun x : Zstar _ => x <? div a x)); cycle 1.
   { intros x; eapply andb_implied_r; rewrite pow_2_r, negb_true_iff, Z.eqb_neq, Hiff; lia. }
   erewrite (filter_ext (fun _ => _ && _) (fun x => div a x <? x)); cycle 1.
   { intros x; apply eq_true_iff_eq. rewrite pow_2_r, !andb_true_iff, !negb_true_iff, Z.eqb_neq, Hiff; lia. }
   trivial. }

  pose proof @NoDup_elements p. (* TODO @ *)
  assert (NoDup roots) as NDroots by eauto using NoDup_filter.
  assert (NoDup smalls) by eauto using NoDup_filter.
  assert (NoDup larges) by eauto using NoDup_filter.

  (* Pairing inverses *)
  assert (HPP : Permutation larges (map (fun x : Zstar p => div a x) smalls));
    [|rewrite HPP in HP; clear HPP].
  { apply Permutation.NoDup_Permutation; intros; trivial.
    { eapply Injective_map_NoDup; trivial.
      (* TODO: div_inj, inv_inj *)
      intros ? ? E.
      rewrite <-2mul_inv_r in E.
      eapply mul_cancel_l, (f_equal inv) in E.
      rewrite 2 inv_inv in E.
      trivial. }
    cbv [smalls larges].
    rewrite in_map_iff; repeat setoid_rewrite filter_In.
    repeat setoid_rewrite N.ltb_lt.
    assert (Hdiv : forall x y z : Zstar p, div z y = x <-> z = mul x y); [|setoid_rewrite Hdiv].
    { split; intros; subst.
      { rewrite <-mul_inv_r, <-!mul_assoc, mul_inv_same_l, mul_1_r; auto. }
      { rewrite div_mul_l, div_same, mul_1_r; trivial. } }
    split.
    { intros []. exists (div a x). rewrite mul_div_r_same_r, div_div_r_same. intuition apply in_elements. }
    { intros (y&A&?&?). rewrite A in *. rewrite mul_comm.
      rewrite div_mul_l, div_same, mul_1_r in *. intuition apply in_elements. } }
  erewrite prod_Permutation, prod_app by eapply HP.
  erewrite (prod_Permutation (smalls++_) (flat_map (fun x => [x;a/x]) smalls)); cycle 1.
  { generalize (div a) as f; generalize smalls as xs; generalize (Zstar p) as A; clear.
    induction xs; cbn [map flat_map app]; intros; econstructor.
    erewrite <-Permutation_middle; eauto. }
  erewrite prod_flat_map, map_ext, map_const, (prod_repeat a); cycle 1.
  { intros x. cbn [prod fold_right]. rewrite mul_1_r, mul_div_r_same_r; trivial. }

  (* Counting elements *)
  assert (length (elements p) = length roots + 2*length smalls)%nat as HL.
  { erewrite Permutation.Permutation_length, !length_app, !length_map by eauto; lia. }
  assert (Z.of_nat (length smalls) = (p-1-Z.of_nat (length roots))/2)%Z as ->.
  { pose proof length_elements_prime p Hp.
    zify; Z.to_euclidean_division_equations; lia. }

  (* Casework on [length roots] using [NoDup roots] *)
  destruct roots as [|x roots'] eqn:A. (* no roots *)
  { cbn [prod fold_right length Nat.eqb of_bool]; rewrite ?mul_1_l, Z.sub_0_r; trivial. }
  assert (Hx: In x roots). { rewrite A. left. split. } apply filter_In, proj2 in Hx.
  destruct roots' as [|y roots''] eqn:B. (* 1 *)
  { unshelve ecase (opp_distinct_odd _ _ x); try lia; auto using Z.prime_odd.
    assert (In (opp x) roots) as AA.
    { apply filter_In, conj; try apply in_elements. rewrite pow_opp_2; trivial. }
    rewrite A in AA; inversion AA as [|AAA]; trivial; inversion AAA. }
  (* 2 <= *)
  assert (Hy: In y roots). { rewrite A. right. left. split. } apply filter_In, proj2 in Hy.
  rewrite eqb_eq in *.
  assert (y = opp x) as ->.
  { case (proj1 (square_roots_opp_prime Hp y x)); trivial.
    { congruence. }
    { intros ->. inversion_clear NDroots as [|? ? X]; case X; left; trivial. } }
  destruct roots'' as [|z roots''']; cycle 1. (* 3 <= *)
  { assert (Hz: In z roots). { rewrite A. right. right. left. split. } apply filter_In, proj2 in Hz.
    rewrite ?eqb_eq in *.
    { case (proj1 (square_roots_opp_prime Hp z x)) as [->| ->].
      { congruence. }
      { inversion_clear NDroots as [|? ? X]; case X; right; left; split. }
      { inversion_clear NDroots as [|? ? ? X].
        inversion_clear X as [|? ? Y]; case Y; left; split. } } }
  (* 2 roots *)
  cbn [prod fold_right length Nat.eqb of_bool];
  repeat rewrite ?mul_1_r, ?mul_1_l, ?mul_opp_l, ?mul_opp_r.
  rewrite <-pow_2_r, Hx, <-pow_succ_r. f_equal. f_equal.
  zify; Z.to_euclidean_division_equations; lia.
Qed.

(** One direction of Wilson's theorem *)
Theorem prod_elements_prime {p : positive} (Hp : Z.prime p) : ∏ elements p = opp one.
Proof.
  rewrite (euler_criterion_subproof Hp one).
  rewrite (proj2 (existsb_exists _ _)), pow_1_l, mul_1_r; cbn [of_bool negb]; trivial.
  exists one; rewrite ?pow_1_l, ?eqb_eq ; auto using in_elements.
Qed.

Lemma euler_criterion_existsb {p : positive} a (Hp : Z.prime p) :
  pow a ((p-1)/2) = of_bool p (existsb (fun x => eqb (pow x 2) a) (elements p)).
Proof.
  pose proof euler_criterion_subproof Hp a as H.
  rewrite prod_elements_prime in H by trivial.
  apply (f_equal opp) in H; rewrite ?of_bool_negb, ?mul_opp_l, ?opp_opp in H.
  case existsb in *; cbn [of_bool] in *;
    rewrite H, ?mul_opp_l, ?opp_opp, ?mul_1_l; trivial.
Qed.

Theorem euler_criterion {p : positive} (a : Zstar p) (Hp : Z.prime p):
  pow a ((p-1)/2) = one <-> exists x, pow x 2 = a.
Proof.
  split.
  { case (Pos.leb_spec 3 p) as []; cycle 1.
    { exists one. apply wlog_eq_Zstar_3_pos; lia. }
    rewrite euler_criterion_existsb, of_bool_1_iff, existsb_exists by trivial.
    intros [[x [_ Hx%eqb_eq]]|]; try lia; eauto. }
  { intros [x Hx]; eapply euler_criterion_square; eauto. }
Qed.

Lemma euler_criterion_nonsquare {p : positive} (Hp : Z.prime p)
  (a : Zstar p) (Ha : forall x, pow x 2 <> a) : pow a ((p-1)/2) = opp one.
Proof.
  rewrite euler_criterion_existsb by trivial.
  case existsb eqn:H; trivial; exfalso.
  apply existsb_exists in H; case H as [x [_ H%eqb_eq]].
  case (Ha x); trivial.
Qed.

Lemma euler_criterion_neq_one {p : positive} (Hp : Z.prime p)
  (a : Zstar p) (H : pow a ((p-1)/2) <> one) : forall x, pow x 2 <> a.
Proof.
  rewrite euler_criterion in H by trivial; intros x Hx; case H; eauto.
Qed.

Lemma euler_criterion_m1 {p : positive} (Hp : Z.prime p) (Hp' : 3 <= p)
  (a : Zstar p) (H : pow a ((p-1)/2) = opp one) : forall x, pow x 2 <> a.
Proof.
  apply euler_criterion_neq_one; trivial; rewrite H; apply opp_1_neq_1; trivial.
Qed.
End Zstar.

Module Zmod.
Import ZstarBase ZmodDef.Zmod ZmodBase.Zmod Zmod Elements.Zmod.
Local Infix "*" := mul.
Local Infix "^" := pow.

Theorem euler_criterion_square_nz {p : positive} (Hp : Z.prime p)
  (a sqrt_a : Zmod p) (Ha : pow sqrt_a 2 = a) (Hnz : a <> zero) :
  pow a ((p-1)/2) = one.
Proof.
  assert (sqrt_a <> zero). { intros ->; rewrite pow_0_l in *; congruence. }
  rewrite <-to_Z_0_iff in *; pose proof to_Z_range a; pose proof to_Z_range sqrt_a.
  assert (Z.coprime a p). { symmetry; apply Z.coprime_prime_small; trivial; lia. }
  assert (Z.coprime sqrt_a p). { symmetry; apply Z.coprime_prime_small; trivial; lia. }
  unshelve epose proof
    (E := Zstar.euler_criterion_square Hp (Zstar.of_Zmod a) (Zstar.of_Zmod sqrt_a) _).
  { apply Zstar.to_Zmod_inj; rewrite Zstar.to_Zmod_pow, 2Zstar.to_Zmod_of_Zmod; trivial. }
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in E; trivial.
Qed.

Theorem euler_criterion_square {p : positive} (Hp : Z.prime p)
  (a sqrt_a : Zmod p) (Ha : pow sqrt_a 2 = a) :
  a = zero \/ pow a ((p-1)/2) = one.
Proof.
  pose proof euler_criterion_square_nz Hp _ _ Ha.
  case (eqb_spec a zero); intuition idtac.
Qed.

Theorem euler_criterion {p : positive} a (Hp : Z.prime p) :
  (a = zero \/ a ^ ((p - 1) / 2) = one) <-> exists x : Zmod p, pow x 2 = a.
Proof.
  split; cycle 1.
  { intros []; eauto using euler_criterion_square. }
  intros [].
  { subst. exists zero. trivial. }
  pose proof (Z.prime_ge_2 _ Hp) as Hp'; pose proof one_neq_zero (m:=p) ltac:(lia).
  case (Pos.eq_dec p 2) as [->|]. {
    pose proof in_elements a ltac:(lia) as C; case C as [<-| [<-| [] ] ];
      [exists zero|exists one]; trivial. }
  assert (((p - 1) / 2) <> 0)%Z by (zify; Z.div_mod_to_equations; nia).
  assert (a <> zero). { intros ->; rewrite pow_0_l in *. congruence. lia. }
  rewrite <-to_Z_0_iff in H2; pose proof to_Z_range a.
  assert (Z.coprime a p). { symmetry; apply Z.coprime_prime_small; trivial; lia. }
  case (proj1 (@Zstar.euler_criterion p (Zstar.of_Zmod a) Hp)) as [x Hx].
  { apply Zstar.to_Zmod_inj.
    rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1; trivial. }
  { exists x. apply (f_equal Zstar.to_Zmod) in Hx.
    rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod in Hx; trivial. }
Qed.

End Zmod.
