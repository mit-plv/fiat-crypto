Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
Require Import Coq.NArith.NArith Coq.PArith.BinPosDef.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Algebra.
Import Monoid.

Local Open Scope equiv_scope.

Generalizable All Variables.
Section IterAssocOp.
  Context {T eq op id} {moinoid : @monoid T eq op id}
          {scalar : Type} (scToN : scalar -> N)
          (testbit : scalar -> nat -> bool)
          (testbit_spec : forall x i, testbit x i = N.testbit_nat (scToN x) i).

  Fixpoint nat_iter_op n a : T :=
    match n with
    | 0%nat => id
    | S n' => op a (nat_iter_op n' a)
    end.

  Lemma nat_iter_op_plus : forall m n a,
    op (nat_iter_op m a) (nat_iter_op n a) === nat_iter_op (m + n) a.
  Proof.
    induction m; intros; simpl; rewrite ?left_identity, <-?IHm, ?associative; reflexivity.
  Qed.

  Definition N_iter_op n a :=
    match n with
    | 0%N => id
    | Npos p => Pos.iter_op op p a
    end.

  Lemma Pos_iter_op_succ : forall p a, Pos.iter_op op (Pos.succ p) a === op a (Pos.iter_op op p a).
  Proof.
   induction p; intros; simpl; rewrite ?associative, ?IHp; reflexivity.
  Qed.

  Lemma N_iter_op_succ : forall n a, N_iter_op (N.succ n) a  === op a (N_iter_op n a).
  Proof.
    destruct n; simpl; intros; rewrite ?Pos_iter_op_succ, ?right_identity; reflexivity.
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

  Definition test_and_op sc a (state : nat * T) :=
    let '(i, acc) := state in
    let acc2 := op acc acc in
    match i with
    | O => (0, acc)
    | S i' => (i', if testbit sc i' then op a acc2 else acc2)
    end.

  Definition iter_op bound sc a : T :=
    snd (funexp (test_and_op sc a) (bound, id) bound).

  Definition test_and_op_inv sc a (s : nat * T) :=
    snd s === nat_iter_op (N.to_nat (N.shiftr_nat (scToN sc) (fst s))) a.

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

  Lemma Nshiftr_succ : forall n i,
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

  Lemma test_and_op_inv_step : forall sc a s,
    test_and_op_inv sc a s ->
    test_and_op_inv sc a (test_and_op sc a s).
  Proof.
    destruct s as [i acc].
    unfold test_and_op_inv, test_and_op; simpl; intro Hpre.
    destruct i; [ apply Hpre | ].
    simpl.
    rewrite Nshiftr_succ.
    case_eq (testbit sc i); intro testbit_eq; simpl;
      rewrite testbit_spec in testbit_eq; rewrite testbit_eq;
      rewrite Hpre, <- plus_n_O, nat_iter_op_plus; reflexivity.
  Qed.

  Lemma test_and_op_inv_holds : forall sc a i s,
    test_and_op_inv sc a s ->
    test_and_op_inv sc a (funexp (test_and_op sc a) s i).
  Proof.
    induction i; intros; auto; simpl; apply test_and_op_inv_step; auto.
  Qed.

  Lemma funexp_test_and_op_index : forall n a x acc y,
    fst (funexp (test_and_op n a) (x, acc) y) === x - y.
  Proof.
    induction y; simpl; rewrite <- ?Minus.minus_n_O; try reflexivity.
    match goal with |- context[funexp ?a ?b ?c] => destruct (funexp a b c) as [i acc'] end.
    simpl in IHy.
    unfold test_and_op.
    destruct i; rewrite Nat.sub_succ_r; subst; rewrite <- IHy; simpl; reflexivity.
  Qed.

  Lemma iter_op_termination : forall sc a bound,
    N.size_nat (scToN sc) <= bound ->
    test_and_op_inv sc a
      (funexp (test_and_op sc a) (bound, id) bound) ->
    iter_op bound sc a === nat_iter_op (N.to_nat (scToN sc)) a.
  Proof.
    unfold test_and_op_inv, iter_op; simpl; intros ? ? ? ? Hinv.
    rewrite Hinv, funexp_test_and_op_index, Minus.minus_diag.
    reflexivity.
  Qed.

  Lemma Nsize_nat_equiv : forall n, N.size_nat n = N.to_nat (N.size n).
  Proof.
    destruct n; auto; simpl; induction p; simpl; auto; rewrite IHp, Pnat.Pos2Nat.inj_succ; reflexivity.
  Qed.

  Lemma Nshiftr_size : forall n bound, N.size_nat n <= bound ->
    N.shiftr_nat n bound = 0%N.
  Proof.
    intros.
    rewrite <- (Nat2N.id bound).
    rewrite Nshiftr_nat_equiv.
    destruct (N.eq_dec n 0); subst; [apply N.shiftr_0_l|].
    apply N.shiftr_eq_0.
    rewrite Nsize_nat_equiv in *.
    rewrite N.size_log2 in * by auto.
    apply N.le_succ_l.
    rewrite <- N.compare_le_iff.
    rewrite N2Nat.inj_compare.
    rewrite <- Compare_dec.nat_compare_le.
    rewrite Nat2N.id.
    auto.
  Qed.

  Lemma iter_op_spec : forall sc a bound, N.size_nat (scToN sc) <= bound ->
    iter_op bound sc a === nat_iter_op (N.to_nat (scToN sc)) a.
  Proof.
    intros.
    apply iter_op_termination; auto.
    apply test_and_op_inv_holds.
    unfold test_and_op_inv.
    simpl.
    rewrite Nshiftr_size by auto.
    reflexivity.
  Qed.

End IterAssocOp.
