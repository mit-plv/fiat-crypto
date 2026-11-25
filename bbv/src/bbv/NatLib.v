Set Loose Hint Behavior "Strict".
Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import Coq.Arith.PeanoNat.Nat.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import bbv.N_Z_nat_conversions.
Require Export bbv.Nomega.

Set Implicit Arguments.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.

Ltac rethink :=
  match goal with
    | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
  induction n; simpl; intuition; rethink.
Qed.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.

Theorem div2_double : forall n, div2 (2 * n) = n.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; f_equal; rethink.
Qed.

Theorem div2_S_double : forall n, div2 (S (2 * n)) = n.
  induction n; simpl; intuition; f_equal; rethink.
Qed.

Notation pow2 := (Nat.pow 2).

Fixpoint Npow2 (n : nat) : N :=
  match n with
    | O => 1
    | S n' => 2 * Npow2 n'
  end%N.

Theorem untimes2 : forall n, n + (n + 0) = 2 * n.
  auto.
Qed.

Section strong.
  Variable P : nat -> Prop.

  Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong' : forall n m, m <= n -> P m.
    induction n; simpl; intuition; apply PH; intuition; auto with *.
    exfalso; lia.
  Qed.

  Theorem strong : forall n, P n.
    intros; eapply strong'; eauto.
  Qed.
End strong.

Theorem div2_odd : forall n,
  mod2 n = true
  -> n = S (2 * div2 n).
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *.
    discriminate.
  destruct n as [|n]; simpl in *; intuition.
  do 2 f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.

Theorem div2_even : forall n,
  mod2 n = false
  -> n = 2 * div2 n.
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  destruct n as [|n]; simpl in *.
    discriminate.
  f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.

Theorem drop_mod2 : forall n k,
  2 * k <= n
  -> mod2 (n - 2 * k) = mod2 n.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition; auto with *.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; lia.
Qed.

Theorem div2_minus_2 : forall n k,
  2 * k <= n
  -> div2 (n - 2 * k) = div2 n - k.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
  destruct k; simpl in *; intuition.

  destruct k; simpl in *; intuition.
  rewrite <- plus_n_Sm.
  apply H; lia.
Qed.

Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= div2 n.
  intros ? n H; case_eq (mod2 n); intro Heq.

  rewrite (div2_odd _ Heq) in H.
  lia.

  rewrite (div2_even _ Heq) in H.
  lia.
Qed.

Lemma two_times_div2_bound: forall n, 2 * Nat.div2 n <= n.
Proof.
  eapply strong. intros n IH.
  destruct n.
  - constructor.
  - destruct n.
    + simpl. constructor. constructor.
    + simpl (Nat.div2 (S (S n))).
      specialize (IH n). lia.
Qed.

Lemma div2_compat_lt_l: forall a b, b < 2 * a -> Nat.div2 b < a.
Proof.
  induction a; intros.
  - lia.
  - destruct b.
    + simpl. lia.
    + destruct b.
      * simpl. lia.
      * simpl.
        apply Nat.lt_succ_r. apply IHa. lia.
Qed.

(* otherwise b is made implicit, while a isn't, which is weird *)
Arguments div2_compat_lt_l {_} {_} _.

Lemma pow2_add_mul: forall a b,
  pow2 (a + b) = (pow2 a) * (pow2 b).
Proof.
  induction a; destruct b; firstorder auto with arith; simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_1_r; auto.
  repeat rewrite Nat.add_0_r.
  rewrite IHa.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_add_distr_r; auto.
Qed.

Lemma mult_pow2_bound: forall a b x y,
  x < pow2 a -> y < pow2 b -> x * y < pow2 (a + b).
Proof.
  intros.
  rewrite pow2_add_mul.
  apply Nat.mul_lt_mono_nonneg; lia.
Qed.

Lemma mult_pow2_bound_ex: forall a c x y,
  x < pow2 a -> y < pow2 (c - a) -> c >= a -> x * y < pow2 c.
Proof.
  intros.
  replace c with (a + (c - a)) by lia.
  apply mult_pow2_bound; auto.
Qed.

Lemma lt_mul_mono' : forall c a b,
  a < b -> a < b * (S c).
Proof.
  induction c; intros.
  rewrite Nat.mul_1_r; auto.
  rewrite Nat.mul_succ_r.
  apply Nat.lt_lt_add_r.
  apply IHc; auto.
Qed.

Lemma lt_mul_mono : forall a b c,
  c <> 0 -> a < b -> a < b * c.
Proof.
  intros.
  replace c with (S (c - 1)) by lia.
  apply lt_mul_mono'; auto.
Qed.

Lemma zero_lt_pow2 : forall sz, 0 < pow2 sz.
Proof.
  induction sz; simpl; lia.
Qed.

Lemma one_lt_pow2:
  forall n,
    1 < pow2 (S n).
Proof.
  intros.
  induction n.
  simpl; lia.
  remember (S n); simpl.
  lia.
Qed.

Lemma one_le_pow2 : forall sz, 1 <= pow2 sz.
Proof.
  intros. pose proof (zero_lt_pow2 sz). lia.
Qed.

Lemma pow2_ne_zero: forall n, pow2 n <> 0.
Proof.
  intros.
  pose proof (zero_lt_pow2 n).
  lia.
Qed.

Lemma mul2_add : forall n, n * 2 = n + n.
Proof.
  induction n; firstorder auto with zarith.
Qed.

Lemma pow2_le_S : forall sz, (pow2 sz) + 1 <= pow2 (sz + 1).
Proof.
  induction sz; simpl; auto.
  repeat rewrite Nat.add_0_r.
  rewrite pow2_add_mul.
  repeat rewrite mul2_add.
  pose proof (zero_lt_pow2 sz).
  lia.
Qed.

Lemma pow2_bound_mono: forall a b x,
  x < pow2 a -> a <= b -> x < pow2 b.
Proof.
  intros.
  replace b with (a + (b - a)) by lia.
  rewrite pow2_add_mul.
  apply lt_mul_mono; auto.
  pose proof (zero_lt_pow2 (b - a)).
  lia.
Qed.

Lemma pow2_inc : forall n m, n < m -> pow2 n < pow2 m.
Proof.
  intros n m; revert n; induction m as [|m IH]; intros n nLm; [lia|].
  destruct n; [now apply one_lt_pow2|].
  assert (H : pow2 n < pow2 m) by (apply IH; lia).
  simpl; lia.
Qed.

Lemma pow2_S: forall x, pow2 (S x) = 2 * pow2 x.
Proof. intros. reflexivity. Qed.

Lemma mod2_S_S : forall n,
  mod2 (S (S n)) = mod2 n.
Proof.
  intros.
  destruct n; auto; destruct n; auto.
Qed.

Lemma mod2_S_not : forall n,
  mod2 (S n) = if (mod2 n) then false else true.
Proof.
  intros.
  induction n; auto.
  rewrite mod2_S_S.
  destruct (mod2 n); replace (mod2 (S n)); auto.
Qed.

Lemma mod2_S_eq : forall n k,
  mod2 n = mod2 k ->
  mod2 (S n) = mod2 (S k).
Proof.
  intros.
  do 2 rewrite mod2_S_not.
  rewrite H.
  auto.
Qed.

Theorem drop_mod2_add : forall n k,
  mod2 (n + 2 * k) = mod2 n.
Proof.
  intros.
  induction n.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by lia.
  apply mod2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by lia.
  apply mod2_S_eq; auto.
Qed.

Lemma mod2sub: forall a b,
  b <= a ->
  mod2 (a - b) = xorb (mod2 a) (mod2 b).
Proof.
  intros. remember (a - b) as c. revert dependent b. revert a. revert c.
  change (forall c,
    (fun c => forall a b, b <= a -> c = a - b -> mod2 c = xorb (mod2 a) (mod2 b)) c).
  apply strong.
  intros c IH a b AB N.
  destruct c.
  - assert (a=b) by lia. subst. rewrite Bool.xorb_nilpotent. reflexivity.
  - destruct c.
    + assert (a = S b) by lia. subst a. simpl (mod2 1). rewrite mod2_S_not.
      destruct (mod2 b); reflexivity.
    + destruct a; [lia|].
      destruct a; [lia|].
      simpl.
      apply IH; lia.
Qed.

Theorem mod2_pow2_twice: forall n,
  mod2 (pow2 n + (pow2 n + 0)) = false.
Proof.
  intros.
  replace (pow2 n + (pow2 n + 0)) with (2 * pow2 n) by lia.
  apply mod2_double.
Qed.

Theorem div2_plus_2 : forall n k,
  div2 (n + 2 * k) = div2 n + k.
Proof.
  induction n; intros.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by lia.
  apply div2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by lia.
  destruct (Even_Odd_dec n).
  - rewrite <- Even_div2.
    rewrite <- Even_div2 by auto.
    apply IHn.
    apply Even_Even_add; auto.
    apply Even_mul_l. now exists 1.
  - rewrite <- Odd_div2.
    rewrite <- Odd_div2 by auto.
    rewrite IHn.
    lia.
    apply Odd_add_l; auto.
    now exists k.
Qed.

Lemma pred_add:
  forall n, n <> 0 -> pred n + 1 = n.
Proof.
  intros n Hn. rewrite add_1_r. exact (succ_pred n Hn).
Qed.

Lemma pow2_zero: forall sz, (pow2 sz > 0)%nat.
Proof.
  induction sz; simpl; auto; lia.
Qed.

Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = pow2 n.
  induction n as [|n IHn]; simpl; intuition.
  rewrite <- IHn; clear IHn.
  case_eq (Npow2 n); intuition; zify; intuition; auto with *.
Qed.

Theorem pow2_N : forall n, Npow2 n = N.of_nat (pow2 n).
Proof.
  intro n. apply nat_of_N_eq. rewrite Nat2N.id. apply Npow2_nat.
Qed.

Lemma Z_of_N_Npow2: forall n, Z.of_N (Npow2 n) = (2 ^ Z.of_nat n)%Z.
Proof.
  intros.
  rewrite pow2_N.
  rewrite nat_N_Z.
  rewrite Nat2Z.inj_pow.
  reflexivity.
Qed.

Lemma pow2_S_z:
  forall n, Z.of_nat (pow2 (S n)) = (2 * Z.of_nat (pow2 n))%Z.
Proof.
  intros.
  replace (2 * Z.of_nat (pow2 n))%Z with
      (Z.of_nat (pow2 n) + Z.of_nat (pow2 n))%Z by lia.
  simpl.
  repeat rewrite Nat2Z.inj_add.
  ring.
Qed.

Lemma pow2_le:
  forall n m, (n <= m)%nat -> (pow2 n <= pow2 m)%nat.
Proof.
  intros.
  assert (exists s, n + s = m) by (exists (m - n); lia).
  destruct H0; subst.
  rewrite pow2_add_mul.
  pose proof (pow2_zero x).
  replace (pow2 n) with (pow2 n * 1) at 1 by lia.
  apply mul_le_mono_l.
  lia.
Qed.

Lemma Zabs_of_nat:
  forall n, Z.abs (Z.of_nat n) = Z.of_nat n.
Proof.
  unfold Z.of_nat; intros.
  destruct n; auto.
Qed.

Lemma Npow2_not_zero:
  forall n, Npow2 n <> 0%N.
Proof.
  induction n; simpl; intros; [discriminate|].
  destruct (Npow2 n); auto.
  discriminate.
Qed.

Lemma Npow2_S:
  forall n, Npow2 (S n) = (Npow2 n + Npow2 n)%N.
Proof.
  simpl; intros.
  destruct (Npow2 n); auto.
  rewrite <-Pos.add_diag.
  reflexivity.
Qed.

Lemma Npow2_pos: forall a,
    (0 < Npow2 a)%N.
Proof.
  intros.
  destruct (Npow2 a) eqn: E.
  - exfalso. apply (Npow2_not_zero a). assumption.
  - constructor.
Qed.

Lemma minus_minus: forall a b c,
  c <= b <= a ->
  a - (b - c) = a - b + c.
Proof. intros. lia. Qed.

Lemma even_odd_destruct: forall n,
  (exists a, n = 2 * a) \/ (exists a, n = 2 * a + 1).
Proof.
  induction n.
  - left. exists 0. reflexivity.
  - destruct IHn as [[a E] | [a E]].
    + right. exists a. lia.
    + left. exists (S a). lia.
Qed.

Lemma mul_div_undo: forall i c,
    c <> 0 ->
    c * i / c = i.
Proof.
  intros.
  pose proof (Nat.div_mul_cancel_l i 1 c) as P.
  rewrite Nat.div_1_r in P.
  rewrite Nat.mul_1_r in P.
  apply P; auto.
Qed.

Lemma mod_add_r: forall a b,
    b <> 0 ->
    (a + b) mod b = a mod b.
Proof.
  intros. rewrite <- Nat.add_mod_idemp_r by lia.
  rewrite Nat.mod_same by lia.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma mod2_cases: forall (n: nat), n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros.
  assert (n mod 2 < 2). {
    apply Nat.mod_upper_bound. congruence.
  }
  lia.
Qed.

Lemma div_mul_undo: forall a b,
    b <> 0 ->
    a mod b = 0 ->
    a / b * b = a.
Proof.
  intros.
  pose proof Nat.div_mul_cancel_l as A. specialize (A a 1 b).
  replace (b * 1) with b in A by lia.
  rewrite Nat.div_1_r in A.
  rewrite mul_comm.
  rewrite <- Nat.divide_div_mul_exact; try assumption.
  - apply A; congruence.
  - apply Nat.mod_divide; assumption.
Qed.

Lemma Smod2_1: forall k, S k mod 2 = 1 -> k mod 2 = 0.
Proof.
  intros k C.
  change (S k) with (1 + k) in C.
  rewrite Nat.add_mod in C by congruence.
  pose proof (Nat.mod_upper_bound k 2).
  assert (k mod 2 = 0 \/ k mod 2 = 1) as E by lia.
  destruct E as [E | E]; [assumption|].
  rewrite E in C. simpl in C. discriminate.
Qed.

Lemma mod_0_r: forall (m: nat),
    m mod 0 = match (1 mod 0) with | 0 => 0 | _ => m end.
Proof.
  intros. reflexivity.
Qed.

Lemma sub_mod_0: forall (a b m: nat),
    a mod m = 0 ->
    b mod m = 0 ->
    (a - b) mod m = 0.
Proof.
  intros. assert (m = 0 \/ m <> 0) as C by lia. destruct C as [C | C].
  - subst. rewrite mod_0_r in *. simpl in *. now subst.
  - assert (a - b = 0 \/ b < a) as D by lia. destruct D as [D | D].
    + rewrite D. apply Nat.mod_0_l. assumption.
    + apply Nat2Z.inj.
      rewrite Nat2Z.inj_mod.
      rewrite Nat2Z.inj_sub by lia.
      rewrite Zdiv.Zminus_mod.
      rewrite <-! Nat2Z.inj_mod.
      rewrite H. rewrite H0.
      apply Z.mod_0_l.
      lia.
Qed.

Lemma mul_div_exact: forall (a b: nat),
    b <> 0 ->
    a mod b = 0 ->
    b * (a / b) = a.
Proof.
  intros. edestruct Nat.div_exact as [_ P]; [eassumption|].
  specialize (P H0). symmetry. exact P.
Qed.
