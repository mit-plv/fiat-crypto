From Stdlib Require Import Bool List Lia PeanoNat Arith ZArith.
Import ListNotations.
Local Open Scope nat_scope.

Lemma add_seq a b c : map (Nat.add a) (seq b c) = seq (a+b) c.
Proof.
  revert b; induction c; intros;
    cbn [seq map]; rewrite ?IHc, ?Nat.add_succ_r; trivial.
Qed.

Lemma add_seq_0_l a b : map (Nat.add a) (seq 0 b) = seq a b.
Proof. rewrite add_seq, Nat.add_0_r; trivial. Qed.

Lemma filter_0mod_seq_0_mul : (forall m, m <> 0 -> forall n,
  filter (fun i => i mod m =? 0) (seq 0 (n * m)) = map (Nat.mul m) (seq 0 n))%nat.
Proof.
  intros until n; induction n; intros; trivial; [].
  rewrite Nat.mul_succ_l, Nat.add_comm, seq_app, filter_app, Nat.add_0_l.
  case m as [|pred_m] eqn:pred_m_eq at 2; [contradiction|]; cbn [seq filter].
  rewrite Nat.Div0.mod_0_l, Nat.eqb_refl.
  erewrite filter_ext_in, filter_false; cycle 1.
  { intros ??%in_seq; apply Nat.eqb_neq; intros [[]X]%Nat.Div0.mod_divides; nia. }
  cbn [map "++"]; rewrite Nat.mul_0_r; f_equal.
  erewrite <-add_seq_0_l, filter_map_swap, filter_ext, IHn; cycle 1.
  { intros. rewrite <-Nat.Div0.add_mod_idemp_l, Nat.Div0.mod_same, Nat.add_0_l; trivial. }
  symmetry. rewrite <-add_seq_0_l, 2map_map; apply map_ext; lia.
Qed.

Lemma filter_cong_seq_mul_mul k m (Hm : m <> 0) : forall n s,
  filter (fun i => i mod m =? k mod m) (seq (s*m) (n*m)) = map (fun i => i*m + k mod m) (seq s n).
Proof.
  induction n; trivial; intros.
  rewrite Nat.mul_succ_l, Nat.add_comm, seq_app, filter_app, <-Nat.mul_succ_l, IHn.
  enough (filter _ _ = [_]) as -> by exact eq_refl.
  pose proof Nat.mod_bound_pos k m ltac:(lia) ltac:(lia).
  replace m with ((k mod m) + (1 + (m-(k mod m+1)))) at 2 by lia.
  rewrite ?seq_app, ?filter_app.
  erewrite filter_ext_in, filter_false, filter_ext_in, filter_true, filter_ext_in, filter_false;
    trivial; intros i ?%in_seq; try apply Nat.eqb_eq; try apply Nat.eqb_neq; assert (s = i / m);
      zify; rewrite ?Nat2Z.inj_div, ?Nat2Z.inj_mod in *; Z.to_euclidean_division_equations; nia.
Qed.

Lemma filter_cong_seq k m (Hm : m <> 0) n s :
  filter (fun i => i mod m =? k mod m) (seq s n) =
  filter (fun i : nat => i mod m =? k mod m) (seq s (n mod m)) ++
  map (Nat.add (s mod m + n mod m + (k mod m + m - s mod m + m - n mod m) mod m))
      (map (Nat.mul m) (seq (s / m) (n / m))).
Proof.
  match goal with |- _ = ?R => set R end.
  pose proof Nat.mod_bound_pos s m ltac:(lia) ltac:(lia).
  pose proof Nat.mod_bound_pos n m ltac:(lia) ltac:(lia).
  rewrite (Nat.div_mod n m), Nat.add_comm, seq_app, (Nat.mul_comm m) by lia.
  rewrite (Nat.div_mod s m) at 2 by lia.
  rewrite <-Nat.add_assoc, Nat.add_comm, <-add_seq by lia.
  rewrite filter_app, filter_map_swap.

  unshelve erewrite (Nat.mul_comm m), (filter_ext _ _ _ (seq (_*m) _)), (filter_cong_seq_mul_mul (k mod m+m-s mod m + m - n mod m)) by lia; shelve_unifiable.
  { intros i; apply eq_true_iff_eq; rewrite 2Nat.eqb_eq; split; intros R.
    { rewrite <-R; clear R.
      apply Nat2Z.inj_iff; repeat rewrite ?Nat2Z.inj_mod, ?Nat2Z.inj_mul, ?Nat2Z.inj_add, ?Nat2Z.inj_sub by lia.
      repeat match goal with
             |- context[Z.of_nat ?x] => is_var x; let x' := fresh x "'" in rename x into x';
             set (Z.of_nat x') as x
             end.
      rewrite <-Z.mod_add with (a:=Z.sub _ _) (b:=Z.opp 2) by lia.
      replace ((s mod m + n mod m + i) mod m + m - s mod m + m - n mod m + - (2) * m)%Z
         with ((s mod m + n mod m + i) mod m - (s mod m + n mod m))%Z by lia.
      rewrite Zminus_mod_idemp_l. f_equal. lia. }
    { rewrite <-Nat.Div0.add_mod_idemp_r, R by lia; clear R; rewrite !Nat.Div0.add_mod_idemp_r, ?Zmod_mod.
      apply Nat2Z.inj_iff; repeat rewrite ?Nat2Z.inj_mod, ?Nat2Z.inj_mul, ?Nat2Z.inj_add, ?Nat2Z.inj_sub by lia.
      repeat match goal with
             |- context[Z.of_nat ?x] => is_var x; let x' := fresh x "'" in rename x into x';
             set (Z.of_nat x') as x
             end.
      rewrite <-Z.mod_add with (a:=Z.add _ _) (b:=Z.opp 2) by lia.
      replace (s mod m + n mod m + (k mod m + m - s mod m + m - n mod m) + - (2) * m)%Z
         with (k mod m)%Z by lia.
      apply Z.mod_mod; lia.  } }

  erewrite map_map, map_ext, <-map_map with
    (f:=Nat.mul m)
    (g:=Nat.add(s mod m + n mod m + ((k mod m + m - s mod m + m - n mod m) mod m))).
  2:{ intros i; cbv beta. lia. }

  epose proof fun x => filter_In (fun i : nat => i mod m =? k mod m) x (seq s (n mod m)).
  setoid_rewrite in_seq in H1.

  exact eq_refl.
Qed.

Lemma seq_mul_r s n c : seq s (n*c) = flat_map (fun i => seq (s + i*c) c) (seq O n).
Proof.
  revert s; induction n; intros; rewrite ?flat_map_nil_l, ?Nat.add_0_r; trivial.
  cbn [Nat.mul]; rewrite Nat.add_comm, seq_app.
  rewrite seq_S, flat_map_app, IHn; cbn [flat_map]; rewrite app_nil_r; trivial.
Qed.

Lemma seq_0_mur n c : seq O (n*c) = flat_map (fun i => seq (i*c) c) (seq O n).
Proof. apply seq_mul_r. Qed.
