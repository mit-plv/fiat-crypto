From Stdlib Require Import NArith ZArith ZModOffset Lia ZmodDef Zmod.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.
Require Import Crypto.Util.Factoring.
Require Import Crypto.Util.ZUtil.Coprime.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Arithmetic.ZmodSqrtDef.
Require Import Crypto.Util.ZmodUtil.Elements.
Require Import Crypto.Util.ZmodUtil.EulerCriterion.

Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Local Coercion N.pos : positive >-> N.
Local Coercion Z.of_N : N >-> Z.
Local Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
Local Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

Import ZstarBase ZmodDef.Zmod ZmodBase.Zmod Zmod EulerCriterion.Zmod.
Local Infix "*" := mul.
Local Infix "^" := pow.
Section WithAB.
Local Infix "^" := pow.
Context {m} (phi_m : positive) (a b : Zmod m).
Local Notation chase_sqrt := (@ZmodSqrtDef.chase_sqrt m phi_m a b).
Context (b_spec : b ^ N.div2 phi_m = opp one).
Context (sqrts_1 : forall x : Zmod m, x ^ 2 = one -> x = one \/ x = opp one).
Local Lemma Private_chase_sqrt_correct (apow : positive) (bpow : N) :
  mul (pow a apow) (pow b bpow) = one /\
  (forall k:N, (2^k | apow) -> (2*2^k | bpow)) /\
  (forall k:N, (2^k | apow) -> (2^k | N.div2 phi_m)) ->
  chase_sqrt apow bpow ^ 2 = a.
Proof.
  revert bpow; induction apow; cbn [chase_sqrt]; intros ?; cycle -1.
  { intros (A&B&P).
    rewrite pow_1_r in *.
    rewrite pow_mul_l_nonneg, <-Zmod.pow_mul_r_nonneg, pow_2_r, <-mul_assoc
      by (try apply N2Z.is_nonneg; lia).
    assert (Z.mul (N.div2 bpow) 2 = bpow) as ->. {
      case (B 0%N) as [].
      { exists (xH); cbn. lia. }
      zify; Z.div_mod_to_equations; nia. }
    rewrite A, mul_1_r; trivial. }
  { rewrite pow_mul_l_nonneg, <-2Zmod.pow_mul_r_nonneg
      by (try apply N2Z.is_nonneg; lia).
    assert (Z.mul (Pos.succ apow) 2 = N.succ (xI apow)) as -> by lia; intros (A&B&P).
    assert (Z.mul (N.div2 bpow) 2 = bpow) as ->. {
      case (B 0%N) as [].
      { exists (xI apow); cbn. lia. }
      zify; Z.div_mod_to_equations; nia. }
    rewrite N2Z.inj_succ, pow_succ_r_nonneg, <-mul_assoc, N2Z.inj_pos, A, mul_1_r; trivial; lia. }
  { case (eqb_spec (a^apow * b^N.div2 bpow) one) as [E|E];
      intros (A&B&P); apply IHapow; clear IHapow.
    { split; trivial. split.
      { intros k [d D].
        case (B (N.succ k)) as [x H].
        { exists d. rewrite N2Z.inj_succ, Z.pow_succ_r; lia. }
        exists x.
        rewrite N2Z.inj_succ, Z.pow_succ_r in * by lia.
        zify; Z.div_mod_to_equations; nia. }
      { intros k [x Hx]. apply P. exists (Z.double x). lia. } }
    { split.
      { rewrite N2Z.inj_add, Zmod.pow_add_r_nonneg, mul_assoc, b_spec by apply N2Z.is_nonneg.
        case (sqrts_1 (mul (a^apow) (b^N.div2 bpow))) as [| ->]; try contradiction.
        { rewrite Zmod.pow_mul_l_nonneg, <-2Zmod.pow_mul_r_nonneg, Z.mul_comm
            by (try apply N2Z.is_nonneg; lia).
          assert (Z.mul (N.div2 bpow) 2 = bpow) as ->. {
            case (B 0%N) as [].
            { exists (xO apow); cbn. lia. }
            zify; Z.div_mod_to_equations; nia. }
          apply A. }
        rewrite mul_opp_opp, mul_1_l; trivial. }
      split.
      { intros k [d D].
        case (B (N.succ k)) as [x Bx].
        { exists d. rewrite N2Z.inj_succ, Z.pow_succ_r; lia. }
        case (P (N.succ k)) as [y Py].
        { exists d. rewrite N2Z.inj_succ, Z.pow_succ_r; lia. }
        rewrite N2Z.inj_add; apply Z.divide_add_r.
        { exists x.
          rewrite N2Z.inj_succ, Z.pow_succ_r in * by lia.
          zify; Z.div_mod_to_equations; nia. }
        exists y.
        rewrite Py, N2Z.inj_succ, Z.pow_succ_r; lia. }
      { intros k [x Hx]. apply P. exists (Z.double x). lia. } } }
Qed.
End WithAB.

Local Lemma Private_chase_sqrt_0 : forall m phi_m b apow bpow,
  @ZmodSqrtDef.chase_sqrt m phi_m zero b apow bpow = zero.
Proof.
  induction apow; cbn [ZmodSqrtDef.chase_sqrt]; intros;
    rewrite ?pow_0_l, ?mul_0_l by lia; trivial.
  case eqb; trivial.
Qed.

Lemma sqrtp_given_nonsquare_correct (p : positive) (Hp : Z.prime p)
  b (Hb : b^N.div2 (Pos.pred p) = opp one) :
  forall a, (exists x, x ^ 2 = a) -> @ZmodSqrtDef.sqrtp_given_nonsquare p a b ^ 2 = a.
Proof.
  cbv [ZmodSqrtDef.sqrtp_given_nonsquare]; intros a.
  intros [x H]. apply wlog_eq_Zmod_2_pos; try lia; intros Hp'.
  case (Pos.eq_dec p 2) as [->|]. {
    pose proof in_elements a ltac:(lia) as C; case C as [<-| [<-| [] ] ];
    cbn; rewrite ?mul_0_l, ?mul_1_l; auto. }
  case (euler_criterion_square Hp _ _ H) as [->|E].
  { rewrite Private_chase_sqrt_0; trivial. }
  apply Private_chase_sqrt_correct; trivial.
  { intros. apply Zmod.square_roots_1_prime; trivial. }
  rewrite Zmod.pow_0_r, Zmod.mul_1_r. split; [|split].
  { rewrite <-E; f_equal. zify; Z.to_euclidean_division_equations; nia. }
  { intros. apply Z.divide_0_r. }
  eassert (Z.to_pos _ = N.div2 _ :>Z) as ->; [|eauto].
  zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma nonsquare_correct {p : positive} (Hp : Z.prime p) (Hp' : 3 <= p) :
  nonsquare p ^ ((p-1)/2) = opp one.
Proof.
  cbv [nonsquare].
  case ZmodSqrtDef.find eqn:H.
  { apply find_some in H; rewrite eqb_eq in H; intuition idtac. }
  exfalso.
  pose proof find_none _ _ H as H'; cbv beta in *; clear H; rename H' into H.
  specialize (fun x : Zstar p => (H x (in_elements x ltac:(lia)))).
  setoid_rewrite <-not_true_iff_false in H; setoid_rewrite eqb_eq in H.
  setoid_rewrite <-Zstar.to_Zmod_pow in H.
  setoid_rewrite <-Zstar.to_Zmod_1 in H.
  setoid_rewrite <-Zstar.to_Zmod_opp in H.
  setoid_rewrite Zstar.to_Zmod_inj_iff in H.
  unshelve epose proof @NoDup_incl_length _ _ (map (fun x : Zstar p => Zstar.pow x 2) (Zstar.positives p)) (Zstar.NoDup_elements _) _ as X; cbv [incl] in *.
  { intros a _; specialize (H a).
    rewrite Zstar.euler_criterion_existsb, Zstar.of_bool_m1_iff_ge3 in H by trivial.
    rewrite not_false_iff_true, existsb_exists in H; case H as [x [_ H%Zstar.eqb_eq]].
    apply in_map_iff; exists (Zstar.abs x); auto using Zstar.in_elements.
    rewrite Zstar.pow_abs_2; split; trivial.
    rewrite Zstar.in_positives, Zstar.to_Zmod_abs, signed_abs_odd; try (lia || apply Z.prime_odd; trivial).
    rewrite Z.abs_pos, signed_0_iff. apply Zstar.to_Zmod_nz; lia. }
  rewrite length_map in X.
  rewrite Zstar.length_elements_prime in X by trivial.
  rewrite Zstar.length_positives_prime in X by trivial.
  zify; Z.div_mod_to_equations; nia.
Qed.

Lemma sqrtp_square (p : positive) (Hp : Z.prime p) a :
  (exists x, x ^ 2 = a) -> @sqrtp p a ^ 2 = a.
Proof.
  intros.
  apply wlog_eq_Zmod_2_pos; try lia; intros Hp'.
  case (Pos.eq_dec p 2) as [->|].
  {pose proof in_elements a ltac:(lia) as C; case C as [<-| [<-| [] ] ];
    cbn; rewrite ?mul_0_l, ?mul_1_l; auto. }
  cbv [sqrtp sqrtspl sqrtsp].
  rewrite sqrtp_given_nonsquare_correct, eqb_refl;
    [ cbn [hd]; rewrite pow_abs_2, sqrtp_given_nonsquare_correct | .. ]; trivial;
    rewrite <-nonsquare_correct by (trivial; lia); f_equal;
    zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma abs_sqrtp p (a : Zmod p) : abs (sqrtp a) = sqrtp a.
Proof. cbv [sqrtp sqrtspl sqrtsp]; case eqb; cbn [hd]; rewrite ?abs_abs, ?abs_0; trivial. Qed.

Lemma sqrtp_nonsq (p : positive) (Hp : Z.prime p) a :
  (forall x, x ^ 2 <> a) -> @sqrtp p a = zero.
Proof.
  pose proof sqrtp_square p Hp a.
  cbv [sqrtp sqrtspl sqrtsp] in *; intros X; case eqb eqn:E; trivial.
  cbn [hd] in *; rewrite eqb_eq, pow_abs_2 in *.
  case (fun x => (X (ZmodSqrtDef.sqrtp_given_nonsquare a (nonsquare p))) (H x)); eauto.
Qed.

Lemma lift_sqrt (q : Z) a x y
  (Hq : 3 <= q)
  (Hp : q mod 2 = 1)
  (Hx : Z.coprime x q)
  (Ha : x^2 mod q = a mod q)
  (Hy : y = x + (x^2 - a)/q*Z.invmod (-2*x) q mod q*q) :
  y^2 mod (q^2) = a mod (q^2).
Proof.
  intros.
  case (Z.eq_dec q 1) as [->|]; rewrite ?Z.mod_1_r; trivial.
  eapply Z.cong_iff_0, Z.div_exact, Z.sub_move_r in Ha; try lia.
  set (((x^2 - a) / q)) as c in *.
  subst y.
  rewrite Z.cong_iff_0.
  rewrite <-Z.add_opp_l.
  eassert (-_+_^2=_) as ->. { ring_simplify. trivial. }
  rewrite Z_mod_plus_full, Ha.
  eassert (_+_=(c + 2*x * ((c * Z.invmod (-2*x) q) mod q)) * q)%Z as -> by ring.
  rewrite Z.pow_2_r, Zmult_mod_distr_r.
  rewrite <-Z.add_mod_idemp_r, Z.mul_mod_idemp_r by lia.
  assert ((2 * x * (c * Z.invmod (-2 * x) q)) = -c * (Z.invmod (-2*x) q * (-2*x)))%Z as -> by ring.
  rewrite <-Z.mul_mod_idemp_r by lia.
  rewrite Z.invmod_coprime; [|lia|..]; cycle 1.
  { apply Z.coprime_mul_l; trivial. change (-2) with (Z.opp 2); rewrite Z.coprime_opp_l.
    symmetry; apply Z.coprime_mod_l_iff. rewrite Hp; reflexivity.  }
  rewrite Z.add_mod_idemp_r, Z.mul_1_r, Z.add_opp_r, Z.sub_diag, Z.mul_0_l; lia.
Qed.

Lemma lift_sqrt_2 n (q := (2^n)%Z) a x
  (Hk : 3 <= n)
  (Hx : Z.odd x = true)
  (Ha : x^2 mod q = a mod q)
  (k := (x ^ 2 - a) / 2 ^ n)
  (y := x + 2^(n-1)*k) :
  y^2 mod 2^(n+1) = a mod 2^(n+1).
Proof.
  intros.
  subst q.
  eapply Z.cong_iff_0, Z.div_exact, Z.sub_move_r in Ha; try lia.
  fold k in Ha.
  rewrite Z.cong_iff_0.
  rewrite <-Z.add_opp_l.
  subst y.
  eapply Zmod_divides. lia. eexists.
  etransitivity. ring_simplify. trivial.
  rewrite Ha.
  etransitivity. ring_simplify. trivial.
  rewrite <-Z.pow_mul_r, (ltac:(lia):((n - 1) * 2=(n+1)+(n-3))%Z), Z.pow_add_r by lia.
  transitivity ((2*2^(n-1)*x+2^n*1)* k + 2^(n+1)*(2^(n-3)*k^2)); [ring|].
  rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred by lia.
  transitivity (2^n*(x+1)*k + 2^(n+1)*(2^(n-3)*k^2)); [ring|].
  rewrite (Z.div2_odd x) at 1.
  rewrite Hx; cbn [Z.b2z].
  assert ((2 * Z.div2 x + 1 + 1) = 2^1*(1+Z.div2 x))%Z as -> by lia.
  rewrite (Z.mul_assoc _ (2^1)), <-Z.pow_add_r by lia.
  instantiate (1:=(1 + Z.div2 x) * k + (2 ^ (n - 3) * k ^ 2)). ring.
Qed.

Local Lemma Private_sqrtp2odd'_correct n :
  forall a, a mod 8 = 1 ->
  (ZmodSqrtDef.sqrtp2odd' n a)^2 mod 2^Z.of_nat n = a mod 2^Z.of_nat n.
Proof.
  induction n as [n IH] using lt_wf_ind. intros a Ha.
  do 4 try case n in *; rewrite ?Z.mod_1_r; trivial.
  1,2,3: simpl Z.of_nat; simpl ZmodSqrtDef.sqrtp2odd';
    symmetry; rewrite <-Z.mod_mod_divide with (b:=8), Ha; trivial;
    solve [exists 1; trivial | exists 2; trivial | exists 4; trivial].
  set (S (S (S n))) as n'; specialize (IH n' ltac:(lia) a Ha).
  cbn [ZmodSqrtDef.sqrtp2odd']. cbn [n'].
  rewrite Z.land_comm, Z.land_ones, ?Z.mod_pow_l by lia.
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?Nat2Z.inj_succ, ?Z.pred_succ, <-?Z.add_1_r by lia.
  rewrite Z.mul_comm. eapply lift_sqrt_2; eauto; try lia.
  change 8 with (2^3)%Z in *; apply (f_equal Z.odd) in Ha, IH;
    rewrite ?Zodd_mod, ?Z.mod_mod_divide, ?Z.mod2_square in *;
    try apply Z.divide_pow_same_r; try lia. rewrite IH, Ha; trivial.
Qed.

Lemma sqrtp2odd'_correct {n} (Hnn : 0 <= n) (a : bits n) (Hodd : a mod 2 = 1)
  (Ha : exists x, x^2 mod 2^n = a) :
  Z.land a (Z.ones 3) = 1 /\ (ZmodSqrtDef.sqrtp2odd' (Z.to_nat n) a)^2 mod 2^n = a.
Proof.
  rewrite !Z.land_ones by lia; change (2^3)%Z with 8 in *.
  pose proof to_Z_range a as Hr; pose proof Z.pow_pos_nonneg 2 n ltac:(lia) Hnn.
  case (Z.eqb_spec n 0) as [->|].
  { change (2^0)%Z with 1%Z in *; Z.to_euclidean_division_equations; lia. }
  assert (E : a mod 8 = 1).
  { eapply Z.odd_square_mod_pow2_1mod8 with (n := n); trivial; try lia.
    case Ha as [x Hx]; exists x; rewrite Hx, Z.mod_small; lia. }
  split; trivial.
  unshelve epose proof Private_sqrtp2odd'_correct (Z.to_nat n) a E.
  rewrite Z2Nat.id, (Z.mod_small a) in * by lia; trivial.
Qed.

Section WithP.
  Context (p : positive).
  Local Notation liftSqrtPop := (ZmodSqrtDef.liftSqrtPop p).

  Context (Hp : Z.prime p).
  Local Lemma Private_liftSqrtPop_correct (Hodd : 3 <= p) (x : Z) lgk :
    forall a (Ha : Z.coprime a p) (Hx : x^2 mod p = a mod p)
    (q := Z.pow p (two_power_nat lgk)), liftSqrtPop x lgk a ^ 2 mod q = a mod q.
  Proof.
    pose proof Z.prime_odd _ Hp Hodd as Hp'.
    induction lgk; cbn [ZmodSqrtDef.liftSqrtPop]; intros.
    { rewrite ?two_power_nat_equiv, ?Z.pow_1_r; trivial. }
    rewrite ?two_power_nat_equiv, ?Nat2Z.inj_succ, ?Z.pow_succ_r, ?(Z.mul_comm 2), ?Z.pow_mul_r in * by lia.
    set (p ^ 2 ^ Z.of_nat lgk)%Z as q in *.
    assert (Hpq : (p | q)%Z).
    { subst q. rewrite <-(Z.succ_pred (2 ^ _)), Z.pow_succ_r by lia; apply Z.divide_factor_l. }
    unshelve epose proof (IHlgk (a mod q) _ _) as IHlgk'.
    { rewrite <-Z.coprime_mod_l_iff, Z.mod_mod_divide, Z.coprime_mod_l_iff; trivial. }
    { rewrite Z.mod_mod_divide; trivial. }
    eapply lift_sqrt; rewrite ?IHlgk', ?Zmod_mod; eauto.
    { subst q. transitivity (p^1)%Z; [|eapply Z.pow_le_mono_r]; try lia. }
    { subst q. rewrite <-Z.mod_pow_l, Hp', Z.pow_1_l; trivial; lia. }
    { apply Z.coprime_sqr_l_iff, Z.coprime_mod_l_iff.
      rewrite IHlgk', ?Z.coprime_mod_l_iff. apply Z.coprime_pow_r; trivial; lia. }
  Qed.

  Local Lemma Private_liftSqrtPop_0 lgk : liftSqrtPop 0 lgk 0 = 0.
  Proof.
    induction lgk; cbn [ZmodSqrtDef.liftSqrtPop]; intros; trivial.
    rewrite ?two_power_nat_equiv, Z.mod_0_l, ?IHlgk,
      ?Z.add_0_l, ?Z.sub_0_r, ?Z.pow_0_l, ?Z.div_0_l, ?Z.mul_0_l; lia.
  Qed.

  Local Lemma Private_lift_correct (Hodd : 3 <= p) (k : positive) (q := Pos.pow p k)
    a (Ha : Z.coprime a p) (x : Zmod p) (Hx : pow x 2 = of_Z p a) :
    liftSqrtPop x (Z.to_nat (Z.log2_up k)) a ^ 2 mod q = a mod q.
  Proof.
    cbv [q] in *; rewrite ?Pos2Z.inj_pow in *.
    unshelve epose proof Private_liftSqrtPop_correct Hodd x (Z.to_nat (Z.log2_up k)) a Ha _ as H.
    { apply (f_equal to_Z) in Hx; rewrite unsigned_pow_nonneg_r, unsigned_of_Z in Hx by lia; exact Hx. }
    rewrite two_power_nat_equiv, Z2Nat.id in * by apply Z.log2_up_nonneg.
    remember (p ^ 2 ^ Z.log2_up k)%Z as q'; cbv zeta in *.
    replace (2 ^ Z.log2_up k)%Z with ((2^Z.log2_up k-k)+k) in * by lia;
      rewrite Z.pow_add_r in *; try lia; cycle 1.
    { enough (k <= 2^Z.log2_up k) by lia; eapply Z.log2_log2_up_spec; lia. }
    apply (f_equal (fun x => x mod p^k)) in H.
    rewrite !Z.mod_mod_divide in H; trivial; try (eexists; eauto).
  Qed.

  Lemma sqrtspop_correct (Hodd : 3 <= p) (k : positive) (a : Zmod (p^k))
     (Hsq : exists x, pow x 2 = a) : exists x y, sqrtspop a = Some (x, y) /\ pow x 2 = a /\ pow y 2 = a.
  Proof.
    cbv [sqrtspop].
    case (eqb_spec zero a) as [<-|Hnz].
    { exists zero, zero; rewrite pow_0_l by lia; repeat split. }
    pose proof Z.prime_ge_2 _ Hp.
    pose proof to_Z_range a as Hr.
    assert (Hpk : 0 < p^k) by (apply Z.pow_pos_nonneg; lia).
    assert (Ha : 0 < a).
    { case (Z.eqb_spec a 0) as [E|]; [|lia]. case Hnz; symmetry; apply unsigned_0_iff; exact E. }
    set (v := val _ _) in *.
    case (proj1 (val_iff v p _ ltac:(lia)) eq_refl) as [[x Hx] Hnx].
    assert (Hpv : 0 < p^v) by (apply Z.pow_pos_nonneg; lia).
    assert (Hax : a = Z.mul (Z.of_N x) (Z.pow p v) :> Z) by (zify; Z.to_euclidean_division_equations; nia).
    rewrite <-N.negb_even. case N.even eqn:O;
      rewrite <-?not_true_iff_false, N.even_spec in O; cbv [negb]; cycle 1.
    { exfalso. admit. }
    assert (Hcop : Z.coprime (a / p^v) p).
    { symmetry; apply Z.coprime_prime_l; trivial; intros [y Hy].
      eapply (ndivide_val_div p (Z.to_pos a)); try lia; change (val p (Z.to_pos a)) with v.
      assert (0 <= y) by (zify; Z.to_euclidean_division_equations; nia).
      exists (Z.to_N y). zify; Z.to_euclidean_division_equations; nia. }
    assert (Hsq' : exists r : Zmod p, pow r 2 = of_Z p (a / p^v)) by admit.
    assert (HB : nonsquare p ^ N.div2 (Pos.pred p) = opp one).
    { rewrite <-nonsquare_correct by (trivial; lia); f_equal; zify; Z.to_euclidean_division_equations; nia. }
    pose proof sqrtp_given_nonsquare_correct p Hp _ HB _ Hsq' as HR.
    cbv [sqrtsp].
    set (r := ZmodSqrtDef.sqrtp_given_nonsquare (of_Z p (a / p^v)) (nonsquare p)) in *.
    rewrite HR, eqb_refl.
    do 2 eexists; split; trivial.
    pose proof Private_lift_correct Hodd k _ Hcop (abs r) (eq_trans (pow_abs_2 _) HR) as L1.
    pose proof Private_lift_correct Hodd k _ Hcop (opp (abs r)) (eq_trans (pow_opp_2 _) (eq_trans (pow_abs_2 _) HR)) as L2.
    rewrite ?Pos2Z.inj_pow in L1, L2.
    case O as [n Hn].
    assert (Hv2 : N.div2 v = n) by (rewrite Hn, <-N.double_spec, N.div2_double; trivial).
    assert (HL : forall L, Z.modulo (Z.pow L 2) (p^k) = Z.modulo (a / p^v) (p^k) -> pow (of_Z (p^k) L) 2 = of_Z (p^k) (a / p^v)).
    { intros L HL. apply to_Z_inj. rewrite unsigned_pow_nonneg_r, !unsigned_of_Z, Z.mod_pow_l, HL by lia; trivial. }
    assert (HR0 : pow (of_Z (p^k) (p ^ N.div2 v)) 2 = of_Z (p^k) (p^v)).
    { rewrite <-of_Z_pow, <-Z.pow_mul_r by lia; f_equal; f_equal; rewrite Hv2; lia. }
    split; (rewrite pow_mul_l_nonneg, HR0, HL, <-of_Z_mul by (lia || trivial);
      etransitivity; [|apply of_Z_to_Z]; f_equal; rewrite Hax, Z.div_mul by lia; lia).
  Admitted.
End WithP.
