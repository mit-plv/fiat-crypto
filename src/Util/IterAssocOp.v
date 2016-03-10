Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
Require Import Coq.NArith.NArith Coq.PArith.BinPosDef.
Local Open Scope equiv_scope.

Generalizable All Variables.
Section IterAssocOp.
  Context `{Equivalence T}
          (op:T->T->T) {op_proper:Proper (equiv==>equiv==>equiv) op}
          (assoc: forall a b c, op a (op b c) === op (op a b) c)
          (neutral:T)
          (neutral_l : forall a, op neutral a === a)
          (neutral_r : forall a, op a neutral === a).
  Existing Instance op_proper.

  Fixpoint nat_iter_op n a :=
    match n with
    | 0%nat => neutral
    | S n' => op a (nat_iter_op n' a)
    end.

  Lemma nat_iter_op_plus : forall m n a,
    op (nat_iter_op m a) (nat_iter_op n a) === nat_iter_op (m + n) a.
  Proof.
    induction m; intros; simpl; rewrite ?neutral_l, <-?IHm, ?assoc; reflexivity.
  Qed.

  Definition N_iter_op n a :=
    match n with
    | 0%N => neutral
    | Npos p => Pos.iter_op op p a
    end.

  Lemma Pos_iter_op_succ : forall p a, Pos.iter_op op (Pos.succ p) a === op a (Pos.iter_op op p a).
  Proof.
   induction p; intros; simpl; rewrite ?assoc, ?IHp; reflexivity.
  Qed.

  Lemma N_iter_op_succ : forall n a, N_iter_op (N.succ n) a  === op a (N_iter_op n a).
  Proof.
    destruct n; simpl; intros; rewrite ?Pos_iter_op_succ, ?neutral_r; reflexivity.
  Qed.

  Lemma N_iter_op_is_nat_iter_op : forall n a, N_iter_op n a === nat_iter_op (N.to_nat n) a.
  Proof.
    induction n using N.peano_ind; intros; rewrite ?N2Nat.inj_succ, ?N_iter_op_succ, ?IHn; reflexivity.
  Qed.

  Fixpoint funexp {A} (f : A -> A) (a : A) (exp : nat) : A :=
    match exp with
    | O => a
    | S exp' => f (funexp f a exp')
    end.

  Definition test_and_op n a (state : nat * T) :=
    let '(i, acc) := state in
    let acc2 := op acc acc in
    match i with
    | O => (0, acc)
    | S i' => (i', if N.testbit_nat n i' then op a acc2 else acc2)
    end.

  Definition iter_op n a : T := 
    snd (funexp (test_and_op n a) (N.size_nat n, neutral) (N.size_nat n)).

  Definition test_and_op_inv n a (s : nat * T) :=
    snd s === nat_iter_op (N.to_nat (N.shiftr_nat n (fst s))) a.

  Hint Rewrite
    N.succ_double_spec
    N.add_1_r
    Nat2N.inj_succ
    Nat2N.inj_mul
    N2Nat.id: N_nat_conv
 .

  Lemma Nsucc_double_to_nat : forall n,
    N.succ_double n = N.of_nat (S (2 * N.to_nat n)).
  Proof.
    intros.
    replace 2 with (N.to_nat 2) by auto.
    autorewrite with N_nat_conv.
    reflexivity.
  Qed.

  Lemma Ndouble_to_nat : forall n,
    N.double n = N.of_nat (2 * N.to_nat n).
  Proof.
    intros.
    replace 2 with (N.to_nat 2) by auto.
    autorewrite with N_nat_conv.
    reflexivity.
  Qed.

  Lemma shiftr_succ : forall n i,
    N.to_nat (N.shiftr_nat n i) =
    if N.testbit_nat n i
    then S (2 * N.to_nat (N.shiftr_nat n (S i)))
    else (2 * N.to_nat (N.shiftr_nat n (S i))).
  Proof.
    intros.
    rewrite Nshiftr_nat_S.
    case_eq (N.testbit_nat n i); intro testbit_i;
      pose proof (Nshiftr_nat_spec n i 0) as shiftr_n_odd;
      rewrite Nbit0_correct in shiftr_n_odd; simpl in shiftr_n_odd;
      rewrite testbit_i in shiftr_n_odd.
    + pose proof (Ndiv2_double_plus_one (N.shiftr_nat n i) shiftr_n_odd) as Nsucc_double_shift.
      rewrite Nsucc_double_to_nat in Nsucc_double_shift.
      apply Nat2N.inj.
      rewrite Nsucc_double_shift.
      apply N2Nat.id.
    + pose proof (Ndiv2_double (N.shiftr_nat n i) shiftr_n_odd) as Nsucc_double_shift.
      rewrite Ndouble_to_nat in Nsucc_double_shift.
      apply Nat2N.inj.
      rewrite Nsucc_double_shift.
      apply N2Nat.id.
  Qed.

  Lemma test_and_op_inv_step : forall n a s,
    test_and_op_inv n a s ->
    test_and_op_inv n a (test_and_op n a s).
  Proof.
    destruct s as [i acc].
    unfold test_and_op_inv, test_and_op; simpl; intro Hpre.
    destruct i; [ apply Hpre | ].
    simpl.
    rewrite shiftr_succ.
    case_eq (N.testbit_nat n i); intro; simpl; rewrite Hpre, <- plus_n_O, nat_iter_op_plus; reflexivity.
  Qed.

  Lemma test_and_op_inv_holds : forall n a i s,
    test_and_op_inv n a s ->
    test_and_op_inv n a (funexp (test_and_op n a) s i).
  Proof.
    induction i; intros; auto; simpl; apply test_and_op_inv_step; auto.
  Qed.

  Lemma funexp_test_and_op_index : forall n a x acc y,
    fst (funexp (test_and_op n a) (x, acc) y) === x - y.
  Proof.
    induction y; simpl; rewrite <- ?Minus.minus_n_O; try reflexivity.
    destruct (funexp (test_and_op n a) (x, acc) y) as [i acc'].
    simpl in IHy.
    unfold test_and_op.
    destruct i; rewrite NPeano.Nat.sub_succ_r; subst; rewrite <- IHy; simpl; reflexivity.
  Qed.

  Lemma iter_op_termination : forall n a,
    test_and_op_inv n a 
      (funexp (test_and_op n a) (N.size_nat n, neutral) (N.size_nat n)) -> 
    iter_op n a === nat_iter_op (N.to_nat n) a.
  Proof.
    unfold test_and_op_inv, iter_op; simpl; intros ? ? Hinv.
    rewrite Hinv, funexp_test_and_op_index, Minus.minus_diag.
    replace (N.shiftr_nat n 0) with n by auto.
    reflexivity.
  Qed.

  Lemma Nsize_nat_equiv : forall n, N.size_nat n = N.to_nat (N.size n).
  Proof.
    destruct n; auto; simpl; induction p; simpl; auto; rewrite IHp, Pnat.Pos2Nat.inj_succ; reflexivity.
  Qed.

  Lemma Nshiftr_size : forall n, N.shiftr_nat n (N.size_nat n) = 0%N.
  Proof.
    intros.
    rewrite Nsize_nat_equiv.
    rewrite Nshiftr_nat_equiv.
    destruct (N.eq_dec n 0); subst; auto.
    apply N.shiftr_eq_0.
    rewrite N.size_log2 by auto.
    apply N.lt_succ_diag_r.
  Qed.
  
  Lemma iter_op_spec : forall n a, iter_op n a === nat_iter_op (N.to_nat n) a.
  Proof.
    intros.
    apply iter_op_termination.
    apply test_and_op_inv_holds.
    unfold test_and_op_inv.
    simpl.
    rewrite Nshiftr_size.
    reflexivity.
  Qed.

End IterAssocOp.
