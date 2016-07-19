Require Import NPeano NArith PArith Ndigits ZArith Znat.
Require Import List Listize Basics Bool Nsatz.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import WordizeUtil.

Import ListNotations.

Section CustomZ2N.
  Lemma inj_and x y : (0 <= y)%Z -> Z.land (Z.of_N x) y = Z.of_N (N.land x (Z.to_N y)).
  Proof.
    intro H; apply Z.bits_inj_iff'; unfold Z.eqf; intros m H0.
    rewrite Z.land_spec.
    rewrite Z2N.inj_testbit; try assumption.
    rewrite Z2N.inj_testbit; try assumption.
    rewrite N.land_spec.
    repeat rewrite <- N2Z.inj_testbit.
    rewrite (Z2N.id m); try assumption.
    rewrite (Z2N.id y); try assumption.
    reflexivity.
  Qed.

  Lemma inj_shiftr x y :
    (0 <= y)%Z -> Z.shiftr (Z.of_N x) y = Z.of_N (N.shiftr x (Z.to_N y)).
  Proof.
    intro H; apply Z.bits_inj_iff'; unfold Z.eqf; intros m H0.
    rewrite Z.shiftr_spec; try assumption.
    rewrite Z2N.inj_testbit; try omega.
    rewrite Z2N.inj_testbit; try assumption.
    rewrite N.shiftr_spec; try apply N_ge_0.
    rewrite Z2N.inj_add; try assumption.
    reflexivity.
  Qed.
End CustomZ2N.

Section NatEq.
  Definition nateq {ins outs} (f: Curried Z Z ins outs) :=
    {g: Curried N N ins outs | forall (x: list N),
        (curriedToListF 0%N g) x =
        map Z.to_N ((curriedToListF 0%Z f) (map Z.of_N x))}.

  Definition nateq_kill_arg'' {m n}
        (f: Curried Z Z (S m) n)
        (g: forall x, nateq (f (Z.of_N x))): Curried N N (S m) n :=
    fun x => proj1_sig (g x).

  Lemma curriedToListF'_tl: forall {A} ins outs m d
        (f: Curried A A ins outs) (x: list A), (ins <= m)%nat ->
    curriedToListF' (S m) d f x = curriedToListF' m d f (tl x).
  Proof.
    intros until x; intro H.
    induction x as [|x0 xs]; simpl.

    - induction ins as [|ins]; simpl; try reflexivity.
        repeat replace (f match m - _ with | 0 => d | S _ => d end)
                with (f d)
                    by (induction (m - ins), (m - S ins); simpl; intuition).
        rewrite (IHins (f d)); try omega.
        reflexivity.

    - clear IHxs.
        induction ins as [|ins]; simpl; try reflexivity.
        replace (m - S ins) with ((m - ins) - 1) by omega.
        assert (m - ins > 0)%nat as H0 by omega.
        induction (m - ins); simpl; try inversion H0;
        rewrite IHins; try omega.

        + reflexivity.

        + repeat f_equal; omega.
  Qed.

  Lemma nateq_kill_arg': forall {m n: nat}
        (f: Curried Z Z (S m) n)
        (g: forall x : N, nateq (f (Z.of_N x)))
        (x: list N),
    curriedToListF 0%N (nateq_kill_arg'' f g) x =
        map Z.to_N (curriedToListF 0%Z f (map Z.of_N x)).
  Proof.
    intros; unfold nateq_kill_arg'', curriedToListF; simpl in *.
    destruct (g _) as [f' p]; simpl.
    pose proof (p (tl x)) as p'; clear p.
    replace 0%Z with (Z.of_N 0%N) by (simpl; intuition).
    replace (m - m) with O in * by omega.
    rewrite map_nth.
    unfold curriedToListF in p'.
    replace (map Z.of_N (tl x)) with (tl (map Z.of_N x)) in p'.
    replace (curriedToListF' (S m) 0%N f' x)
        with (curriedToListF' m 0%N f' (tl x));
        try rewrite p'; try clear f'; try clear f; try f_equal.

    - rewrite curriedToListF'_tl; try omega.
        repeat f_equal; intuition.

    - rewrite curriedToListF'_tl; try omega.
        rewrite p'.
        reflexivity.

    - induction x; simpl; intuition.
  Qed.

  Definition nateq_kill_arg {m n} (f: Curried Z Z (S m) n):
        (forall x, nateq (f (Z.of_N x))) -> nateq f.
    refine (fun g => exist _ (nateq_kill_arg'' f g) _).
        apply nateq_kill_arg'.
  Defined.

  Definition nateq_break_cons: forall {m} (a: Z) (b: list Z),
    @nateq O 1 [a] ->
    @nateq O (S m) b ->
    @nateq O (S (S m)) (cons a b).
  Proof.
    intros m a b n0 n1.
    exists (@cons N (hd 0%N (proj1_sig n0)) (proj1_sig n1)); intro x.
    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    pose proof (p0 x) as p0'.
    pose proof (p1 x) as p1'.

    abstract (
        unfold curriedToListF in *;
        simpl in *;
        rewrite p0', p1';
        simpl; reflexivity).
  Defined.

  Definition nateq_nil: @nateq O O [].
  Proof. exists []; abstract (intro; simpl; reflexivity). Defined.

  Definition nateq_cut_let: forall {outs} (x: Z) (f: Z -> list Z),
    (0 <= x)%Z ->
    @nateq 1 outs f -> @nateq O 1 [x] ->
    @nateq O outs (Let_In x f).
  Proof.
    intros outs x f H n0 n1.
    exists (Let_In (hd 0%N (proj1_sig n1)) (proj1_sig n0)); intro x0.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    pose proof (p0 [Z.to_N x]) as p0'.
    pose proof (p1 x0) as p1'.

    abstract (
        unfold curriedToListF, Let_In in *;
        simpl in *;
        rewrite p1'; simpl;
        rewrite p0'; simpl;
        f_equal;
        rewrite Z2N.id; intuition).
  Defined.

  Definition nateq_let_const: forall {T outs} (a: T) (f: T -> list Z),
    @nateq O outs (f a) -> @nateq O outs (Let_In a f).
  Proof.
    intros T outs a f n0.
    exists (proj1_sig n0); intro x0.
    destruct n0 as [f0 p0].
    pose proof (p0 x0) as p0'.
    abstract (
        simpl; rewrite p0'; unfold Let_In;
        simpl; reflexivity).
  Defined.

  Definition nateq_debool_andb: forall {outs} (a b: bool) (f: bool -> list Z),
    @nateq O outs (Let_In a (fun x => Let_In b (fun y => f (andb x y)))) ->
    @nateq O outs (Let_In (andb a b) f).
  Proof.
    intros T outs a f n0.
    exists (proj1_sig n0); intro x0.
    destruct n0 as [f0 p0].
    pose proof (p0 x0) as p0'.
    abstract (
        simpl; rewrite p0'; unfold Let_In;
        simpl; reflexivity).
  Defined.

  Definition nateq_debool_ltb: forall {outs} (x y: Z) (f: bool -> list Z),
    (0 <= x)%Z -> (0 <= y)%Z ->
    @nateq O outs (f true) -> @nateq O outs (f false) ->
    @nateq O 1 [x] -> @nateq O 1 [y] ->
    @nateq O outs (Let_In (x <? y)%Z f).
  Proof.
    intros T a b f I0 I1 n0 n1 n2 n3.

    exists (if ((hd 0%N (curriedToListF 0%N (proj1_sig n2) []))
            <? (hd 0%N (curriedToListF 0%N (proj1_sig n3) [])))%N
        then (proj1_sig n0) else (proj1_sig n1)); intro x.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    destruct n2 as [f2 p2].
    destruct n3 as [f3 p3].

    pose proof (p0 x) as p0'.
    pose proof (p1 x) as p1'.
    pose proof (p2 x) as p2'.
    pose proof (p3 x) as p3'.

    abstract (
        unfold Let_In; simpl;
        rewrite p2, p3; simpl;
        unfold Z.ltb, N.ltb;
        rewrite <- N2Z.inj_compare;
        repeat rewrite Z2N.id; try assumption;
        destruct (a ?= b)%Z; try assumption).
  Defined.

  Lemma Zinj_eqb: forall a b,
    (0 <= a)%Z -> (0 <= b)%Z -> (Z.to_N a =? Z.to_N b)%N = (a =? b)%Z.
  Proof.
    intros a b Ha Hb.
    pose proof (Z.eqb_eq a b) as HZ.
    pose proof (N.eqb_eq (Z.to_N a) (Z.to_N b)) as HN.
    destruct (Z.eq_dec a b) as [e|e].

    - assert (Z.to_N a = Z.to_N b) as e' by (rewrite e; reflexivity).
        apply HZ in e.
        apply HN in e'.
        rewrite e, e'; simpl; reflexivity.

    - replace (a =? b)%Z with false.

        + induction (Z.to_N a =? Z.to_N b)%N; try reflexivity.
        pose proof (eq_refl true) as H.
        apply HN in H.
        contradict e.
        rewrite <- (Z2N.id a); try assumption.
        rewrite <- (Z2N.id b); try assumption.
        rewrite H.
        reflexivity.

        + induction (a =? b)%Z; try reflexivity.
        pose proof (eq_refl true) as H.
        apply HZ in H.
        intuition.
  Qed.

  Definition nateq_debool_eqb: forall {outs} (x y: Z) (f: bool -> list Z),
    (0 <= x)%Z -> (0 <= y)%Z ->
    @nateq O outs (f true) -> @nateq O outs (f false) ->
    @nateq O 1 [x] -> @nateq O 1 [y] ->
    @nateq O outs (Let_In (Z.eqb x y) f).
  Proof.
    intros T a b f I0 I1 n0 n1 n2 n3.

    exists (if (N.eqb
            (hd 0%N (curriedToListF 0%N (proj1_sig n2) []))
            (hd 0%N (curriedToListF 0%N (proj1_sig n3) [])))%N
        then (proj1_sig n0) else (proj1_sig n1)); intro x.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    destruct n2 as [f2 p2].
    destruct n3 as [f3 p3].

    pose proof (p0 x) as p0'.
    pose proof (p1 x) as p1'.
    pose proof (p2 x) as p2'.
    pose proof (p3 x) as p3'.

    abstract (
        unfold Let_In; simpl;
        rewrite p2, p3; simpl;
        rewrite Zinj_eqb;
        destruct (a =? b)%Z;
        assumption).
  Defined.
End NatEq.

Ltac standardize_nateq :=
  repeat match goal with
  | [|- @nateq (S ?m) _ _] => apply nateq_kill_arg; intro
  | [|- @nateq O _ (Let_In true _)] => apply nateq_let_const
  | [|- @nateq O _ (Let_In false _)] => apply nateq_let_const
  | [|- @nateq O _ (Let_In (_ <? _)%Z _)] => apply nateq_debool_ltb
  | [|- @nateq O _ (Let_In (_ =? _)%Z _)] => apply nateq_debool_eqb
  | [|- @nateq O _ (Let_In (andb _ _) _)] => apply nateq_debool_andb
  | [|- @nateq O _ (Let_In _ _)] => apply nateq_cut_let
  | [|- @nateq O _ (cons _ _)] => apply nateq_break_cons
  | [|- (_ <= _)%Z ] => omega
  end.

Transparent nateq_kill_arg nateq_let_const nateq_debool_ltb
            nateq_debool_eqb nateq_debool_andb nateq_cut_let
            nateq_break_cons.

Ltac natize_iter :=
  match goal with
  | [ |- context [(Z.of_N ?x + Z.of_N ?y)%Z]] =>
    rewrite <- N2Z.inj_add

  | [ |- context [(Z.of_N ?x - Z.of_N ?y)%Z]] =>
    rewrite <- N2Z.inj_sub

  | [ |- context [(Z.of_N ?x * Z.of_N ?y)%Z]] =>
    rewrite <- N2Z.inj_mul

  | [ |- context [Z.land (Z.of_N ?x) ?y]] =>
    rewrite inj_and

  | [ |- context [Z.shiftr (Z.of_N ?x) ?y]] =>
    rewrite inj_shiftr

  | [ |- context [Z.to_N (Z.of_N ?x)]] =>
    rewrite N2Z.id
  end.

Opaque Z.shiftr Z.shiftl Z.land Z.eqb.

Ltac simpl' := cbn beta delta iota.

Ltac solve_nateq :=
  simpl'; standardize_nateq; simpl';
  eexists; intros; simpl';
  repeat natize_iter; simpl';
  try reflexivity.
