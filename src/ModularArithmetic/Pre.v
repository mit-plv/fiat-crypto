Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.Numbers.BinNums Coq.ZArith.Zdiv Coq.ZArith.Znumtheory.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.omega.Omega.

Lemma Z_mod_mod x m : x mod m = (x mod m) mod m.
  symmetry.
  destruct (BinInt.Z.eq_dec m 0).
  - subst; rewrite !Zdiv.Zmod_0_r; reflexivity.
  - apply BinInt.Z.mod_mod; assumption.
Qed.

Lemma exist_reduced_eq: forall (m : Z) (a b : Z), a = b -> forall pfa pfb,
    exist (fun z : Z => z = z mod m) a pfa =
    exist (fun z : Z => z = z mod m) b pfb.
Proof.
  intuition; simpl in *; try congruence.
  subst_max.
  f_equal.
  eapply UIP_dec, Z.eq_dec.
Qed.

Definition opp_impl:
  forall {m : BinNums.Z},
    {opp0 : {z : BinNums.Z | z = z mod m} -> {z : BinNums.Z | z = z mod m} |
     forall x : {z : BinNums.Z | z = z mod m},
       exist (fun z : BinNums.Z => z = z mod m)
             ((proj1_sig x + proj1_sig (opp0 x)) mod m)
             (Z_mod_mod (proj1_sig x + proj1_sig (opp0 x)) m) =
       exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m)}.
  intro m.
  refine (exist _ (fun x => exist _ ((m-proj1_sig x) mod m) _) _); intros.

  destruct x;
  simpl;
  apply exist_reduced_eq;
  rewrite Zdiv.Zplus_mod_idemp_r;
  replace (x + (m - x)) with m by omega;
  apply Zdiv.Z_mod_same_full.

  Grab Existential Variables.
  destruct x; simpl.
  rewrite Zdiv.Zmod_mod; reflexivity.
Defined.

Definition mulmod m := fun a b => a * b mod m.
Definition powmod_pos m := Pos.iter_op (mulmod m).
Definition powmod m a x := match x with N0 => 1 mod m | Npos p => powmod_pos m p (a mod m) end.

Lemma mulmod_assoc:
  forall m x y z : Z, mulmod m x (mulmod m y z) = mulmod m (mulmod m x y) z.
Proof.
  unfold mulmod; intros.
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
  apply Z.mul_assoc.
Qed.

Lemma powmod_1plus:
      forall m a : Z,
        forall x : N, powmod m a (1 + x) = (a * (powmod m a x mod m)) mod m.
Proof.
  intros m a x.
  rewrite N.add_1_l.
  cbv beta delta [powmod N.succ].
  destruct x. simpl; rewrite ?Zdiv.Zmult_mod_idemp_r, Z.mul_1_r; auto.
  unfold powmod_pos.
  rewrite Pos.iter_op_succ by (apply mulmod_assoc).
  unfold mulmod.
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
Qed.


Lemma N_pos_1plus : forall p, (N.pos p = 1 + (N.pred (N.pos p)))%N.
  intros.
  rewrite <-N.pos_pred_spec.
  rewrite N.add_1_l.
  rewrite N.pos_pred_spec.
  rewrite N.succ_pred; eauto.
  discriminate.
Qed.

Lemma powmod_Zpow_mod : forall m a n, powmod m a n = (a^Z.of_N n) mod m.
Proof.
  induction n using N.peano_ind; [auto|].
  rewrite <-N.add_1_l.
  rewrite powmod_1plus.
  rewrite IHn.
  rewrite Zmod_mod.
  rewrite N.add_1_l.
  rewrite N2Z.inj_succ.
  rewrite Z.pow_succ_r by (apply N2Z.is_nonneg).
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
Qed.

Definition pow_impl_sig {m} : {z : Z | z = z mod m} -> N -> {z : Z | z = z mod m}.
  intros a x.
  exists (powmod m (proj1_sig a) x).
  destruct x; [simpl; rewrite Zmod_mod; reflexivity|].
  rewrite N_pos_1plus.
  rewrite powmod_1plus.
  rewrite Zmod_mod; reflexivity.
Defined.

Definition pow_impl:
   forall {m : BinNums.Z},
   {pow0
   : {z : BinNums.Z | z = z mod m} -> BinNums.N -> {z : BinNums.Z | z = z mod m}
   |
   forall a : {z : BinNums.Z | z = z mod m},
   pow0 a 0%N =
   exist (fun z : BinNums.Z => z = z mod m) (1 mod m) (Z_mod_mod 1 m) /\
   (forall x : BinNums.N,
    pow0 a (1 + x)%N =
    exist (fun z : BinNums.Z => z = z mod m)
      ((proj1_sig a * proj1_sig (pow0 a x)) mod m)
      (Z_mod_mod (proj1_sig a * proj1_sig (pow0 a x)) m))}.
  intros m. exists pow_impl_sig.
  split; [eauto using exist_reduced_eq|]; intros.
  apply exist_reduced_eq.
  rewrite powmod_1plus.
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
Qed.

Lemma mul_mod_modulus_r : forall x m, (x*m) mod m = 0.
  intros.
  rewrite Zmult_mod, Z_mod_same_full.
  rewrite Z.mul_0_r, Zmod_0_l.
  reflexivity.
Qed.

Lemma mod_opp_equiv : forall x y m,  x  mod m = (-y) mod m ->
                              (-x) mod m =   y  mod m.
Proof.
  intros.
  rewrite <-Z.sub_0_l.
  rewrite Zminus_mod. rewrite H.
  rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r; f_equal.
  destruct y; auto.
Qed.

Definition mod_inv_eucl (a m:Z) : Z.
  destruct (euclid a m). (* [euclid] is opaque. TODO: reimplement? *)
  exact ((match a with Z0 => Z0 | _ =>
                                 (match d with Z.pos _ =>  u | _ => -u end)
          end) mod m).
Defined.

Lemma reduced_nonzero_pos:
  forall a m : Z, m > 0 -> a <> 0 -> a = a mod m -> 0 < a.
Proof.
  intros a m m_pos a_nonzero pfa.
  destruct (Z.eq_dec 0 m); subst_max; try omega.
  pose proof (Z_mod_lt a m) as H.
  destruct (Z.eq_dec 0 a); subst_max; try omega.
Qed.

Lemma mod_inv_eucl_correct : forall a m, a <> 0 -> a = a mod m -> prime m ->
                                    ((mod_inv_eucl a m) * a) mod m = 1 mod m.
Proof.
  intros a m a_nonzero pfa prime_m.
  pose proof (prime_ge_2 _ prime_m).
  assert (0 < m) as m_pos by omega.
  assert (0 <= m) as m_nonneg by omega.
  assert (0 < a) as a_pos by (eapply reduced_nonzero_pos; eauto; omega).
  unfold mod_inv_eucl.
  destruct a as [|a'|a'] eqn:ha; try pose proof (Zlt_neg_0 a') as nnn; try omega; clear nnn.
  rewrite<- ha in *.
  lazymatch goal with [ |- context [euclid ?a ?b] ] => destruct (euclid a b) end.
  lazymatch goal with [H: Zis_gcd _ _ _ |- _ ] => destruct H end.
  rewrite Z.add_move_r in e.
  destruct (Z_mod_lt a m ); try omega; rewrite <- pfa in *.
  destruct (prime_divisors _ prime_m _ H1) as [Ha|[Hb|[Hc|Hd]]]; subst d.
  + assert ((u * a) mod m = (-1 - v * m) mod m) as Hx by (f_equal; trivial).
    rewrite Zminus_mod, mul_mod_modulus_r, Z.sub_0_r, Zmod_mod in Hx.
    rewrite Zmult_mod_idemp_l.
    rewrite <-Zopp_mult_distr_l.
    eauto using mod_opp_equiv.
  + rewrite Zmult_mod_idemp_l.
    rewrite e, Zminus_mod, mul_mod_modulus_r, Z.sub_0_r, Zmod_mod; reflexivity.
  + pose proof (Zdivide_le _ _ m_nonneg a_pos H0); omega.
  + apply Zdivide_opp_l_rev in H0.
    pose proof (Zdivide_le _ _ m_nonneg a_pos H0); omega.
Qed.

Lemma mod_inv_eucl_sig : forall {m}, {z : Z | z = z mod m} -> {z : Z | z = z mod m}.
  intros m a.
  exists (mod_inv_eucl (proj1_sig a) m).
  destruct a; unfold mod_inv_eucl.
  lazymatch goal with [ |- context [euclid ?a ?b] ] => destruct (euclid a b) end.
  rewrite Zmod_mod; reflexivity.
Defined.

Definition inv_impl :
   forall {m : BinNums.Z},
   {inv0 : {z : BinNums.Z | z = z mod m} -> {z : BinNums.Z | z = z mod m} |
   inv0 (exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m)) =
   exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m) /\
   (Znumtheory.prime m ->
    forall a : {z : BinNums.Z | z = z mod m},
    a <> exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m) ->
    exist (fun z : BinNums.Z => z = z mod m)
      ((proj1_sig a * proj1_sig (inv0 a)) mod m)
      (Z_mod_mod (proj1_sig a * proj1_sig (inv0 a)) m) =
    exist (fun z : BinNums.Z => z = z mod m) (1 mod m) (Z_mod_mod 1 m))}.
Proof.
  intros m. exists mod_inv_eucl_sig. split; intros.
  - simpl.
    apply exist_reduced_eq; simpl.
    unfold mod_inv_eucl; simpl.
    lazymatch goal with [ |- context [euclid ?a ?b] ] => destruct (euclid a b) end.
    auto.
  -
    destruct a.
    cbv [proj1_sig mod_inv_eucl_sig].
    rewrite Z.mul_comm.
    eapply exist_reduced_eq.
    rewrite mod_inv_eucl_correct; eauto.
    intro; destruct H0.
    eapply exist_reduced_eq. congruence.
Qed.
