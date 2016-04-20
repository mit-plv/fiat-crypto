Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.BaseSystem Crypto.BaseSystemProofs.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.

Local Open Scope Z.

Definition testbit (limb_width n : nat) (us : list Z) :=
  Z.testbit (nth_default 0 us (n / limb_width)) (Z.of_nat (n mod limb_width)).

(* identical limb widths *)
Definition uniform_base (l : list Z) r := forall n d, (n < length l)%nat ->
  nth n l d = r ^ (Z.of_nat n).

Definition successive_powers (l : list Z) r := forall n d, (S n < length l)%nat ->
  nth (S n) l d = r * nth n l d.

Fixpoint unfold_bits (limb_width : Z) (us : list Z) :=
  match us with
  | nil => 0
  | u0 :: us' => Z.land u0 (Z.ones limb_width) + Z.shiftl (unfold_bits limb_width us') limb_width
  end.

Lemma uniform_base_first : forall b0 bs r,
  uniform_base (b0 :: bs) r -> b0 = 1.
Proof.
  boring.
  match goal with
  | [ H : uniform_base _ _ |- _ ] => unfold uniform_base in H;
    specialize (H 0%nat 0); simpl in H; eapply H; omega
  end.
Qed.

Lemma uniform_base_second : forall b0 b1 bs r,
  uniform_base (b0 :: b1 :: bs) r -> b1 = r.
Proof.
  boring.
  match goal with
  | [ H : uniform_base _ _ |- _ ] => unfold uniform_base in H;
    specialize (H 1%nat 0); cbv [nth length] in H;
    rewrite Z.pow_1_r in H; apply H; omega
  end.
Qed.


Lemma successive_powers_second : forall b0 b1 bs r,
  successive_powers (b0 :: b1 :: bs) r -> b1 = r * b0.
Proof.
  boring.
  match goal with
  | [ H : successive_powers _ _ |- _ ] => unfold uniform_base in H;
    specialize (H 0%nat 0); cbv [nth length] in H; apply H; omega
  end.
Qed.

Ltac uniform_base_subst :=
  match goal with
  | [H : uniform_base (?b0 :: ?b1 :: _) _ |- _ ]=>
      erewrite (uniform_base_first  b0); eauto;
      erewrite (uniform_base_second b0 b1); eauto
  end.

Lemma successive_powers_tail : forall x0 xs r, successive_powers (x0 :: xs) r ->
  successive_powers xs r.
Proof.
  unfold successive_powers; boring.
Qed.

Lemma decode_uniform_shift : forall us base limb_width, (S (length us) <= length base)%nat ->
  successive_powers base (2 ^ limb_width) ->
  decode base (mul_each (2 ^ limb_width) us) = decode base (0 :: us).
Proof.
  unfold decode, decode', accumulate, mul_each;
    induction us; induction base; try solve [boring].
  intros; simpl in *.
  destruct base; [ boring; omega | ].
  simpl; f_equal.
  + erewrite (successive_powers_second _ z); eauto.
    ring.
  + apply IHus; [ omega | ].
    eapply successive_powers_tail; eassumption.
Qed.

Lemma uniform_base_successive_powers : forall xs r, uniform_base xs r ->
  successive_powers xs r.
Proof.
  unfold uniform_base, successive_powers; intros ? ? G n ? ?.
  do 2 rewrite G by omega.
  rewrite Nat2Z.inj_succ.
  apply Z.pow_succ_r.
  apply Nat2Z.is_nonneg.
Qed.

Lemma uniform_base_BaseVector : forall base r, (r > 0) -> (0 < length base)%nat ->
  uniform_base base r -> BaseVector base.
Proof.
  unfold uniform_base.
  intros ? ? r_gt_0 base_nonempty uniform.
  constructor.
  + intros b In_b_base.
    apply In_nth_error_value in In_b_base.
    destruct In_b_base as [x nth_error_x].
    pose proof (nth_error_value_length _ _ _ _ nth_error_x) as index_bound.
    specialize (uniform x 0 index_bound).
    rewrite <- nth_default_eq in uniform.
    erewrite nth_error_value_eq_nth_default in uniform; eauto.
    subst.
    destruct r; [ | apply pos_pow_nat_pos | pose proof (Zlt_neg_0 p) ] ; omega.
  + intros.
    rewrite nth_default_eq.
    rewrite uniform; auto.
  + intros.
    subst b.
    subst r0.
    repeat rewrite nth_default_eq.
    repeat rewrite uniform by omega; auto.
    rewrite <- Z.pow_add_r by apply Nat2Z.is_nonneg.
    rewrite Nat2Z.inj_add.
    rewrite <- Z.pow_sub_r, <- Z.pow_add_r by omega.
    f_equal.
    omega.
Qed.

Definition no_overflow us limb_width := forall n,
  Z.land (nth_default 0 us n) (Z.ones limb_width) = nth_default 0 us n.

Lemma no_overflow_cons : forall u0 us limb_width,
  no_overflow (u0 :: us) limb_width -> Z.land u0 (Z.ones limb_width) = u0.
Proof.
  unfold no_overflow; intros ? ? ? no_overflow_u0_us.
  specialize (no_overflow_u0_us 0%nat).
  rewrite nth_default_cons in no_overflow_u0_us.
  assumption.
Qed.

Lemma no_overflow_tail : forall u0 us limb_width,
  no_overflow (u0 :: us) limb_width -> no_overflow us limb_width.
Proof.
  unfold no_overflow; intros.
  erewrite <- nth_default_cons_S; eauto.
Qed.

Lemma unfold_bits_decode : forall limb_width us base, (0 <= limb_width) ->
  (length us <= length base)%nat -> (0 < length base)%nat ->
  no_overflow us limb_width ->
  uniform_base base (2 ^ limb_width) ->
  BaseSystem.decode base us = unfold_bits limb_width us.
Proof.
  induction us; boring.
  rewrite <- (IHus base) by (omega || eauto using no_overflow_tail).
  rewrite decode_cons by (eapply uniform_base_BaseVector; eauto;
    rewrite gt_lt_symmetry; apply Z_pow_gt0; omega).
  simpl.
  f_equal.
  + symmetry. eapply no_overflow_cons; eauto.
  + rewrite Z.shiftl_mul_pow2 by assumption.
    erewrite <- decode_uniform_shift; eauto using uniform_base_successive_powers.
    rewrite mul_each_rep.
    unfold decode.
    apply Z.mul_comm.
Qed.


Lemma unfold_bits_indexing : forall us i limb_width, (0 < limb_width)%nat ->
  no_overflow us (Z.of_nat limb_width) ->
  nth_default 0 us i =
  Z.land (Z.shiftr (unfold_bits (Z.of_nat limb_width) us) (Z.of_nat (i * limb_width))) (Z.ones (Z.of_nat limb_width)).
Proof.
  induction us; intros.
  + rewrite nth_default_nil.
    rewrite Z.shiftr_0_l.
    auto using Z.land_0_l.
  + destruct i; simpl.
    - rewrite nth_default_cons.
      rewrite Z.shiftr_0_r, Z_land_add_land by omega.
      symmetry; eapply no_overflow_cons; eauto.
    - rewrite nth_default_cons_S.
      erewrite IHus; eauto using no_overflow_tail.
      remember (i * limb_width)%nat as k.
      rewrite Z_shiftr_add_land by omega.
      replace (limb_width + k - limb_width)%nat with k by omega.
      reflexivity.
Qed.

Lemma unfold_bits_testbit : forall limb_width us n, (0 < limb_width)%nat ->
  no_overflow us (Z.of_nat limb_width) ->
  testbit limb_width n us = Z.testbit (unfold_bits (Z.of_nat limb_width) us) (Z.of_nat n).
Proof.
  unfold testbit; intros.
  erewrite unfold_bits_indexing; eauto.
  rewrite <- Z_testbit_low by
    (split; try apply Nat2Z.inj_lt; pose proof (mod_bound_pos n limb_width); omega).
  rewrite Z.shiftr_spec by apply Nat2Z.is_nonneg.
  f_equal.
  rewrite <- Nat2Z.inj_add.
  apply Z2Nat.inj; try apply Nat2Z.is_nonneg.
  rewrite !Nat2Z.id.
  symmetry.
  rewrite Nat.add_comm, Nat.mul_comm.
  apply Nat.div_mod; omega.
Qed.

Lemma testbit_spec : forall n us base limb_width, (0 < limb_width)%nat ->
  (0 < length base)%nat -> (length us <= length base)%nat ->
  no_overflow us (Z.of_nat limb_width) ->
  uniform_base base (2 ^ (Z.of_nat limb_width)) ->
  testbit limb_width n us = Z.testbit (BaseSystem.decode base us) (Z.of_nat n).
Proof.
  intros.
  erewrite unfold_bits_testbit, unfold_bits_decode; eauto; omega.
Qed.