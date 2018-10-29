Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Local Open Scope Z_scope.

(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)

(* TODO : PolynomialRing shouldn't rely on F directly; take in an arbitrary field *)
Module Lists.
  Section associational.
    Context {q : BinNums.positive}.

    Definition multerm (a : list (F q * nat)) (x : F q * nat) : list (F q * nat) :=
      List.map (fun y => (F.mul (fst x) (fst y), (snd x + snd y)%nat)) a.
    Definition assoc_mul (a b : list (F q * nat)) : list (F q * nat) := List.flat_map (multerm b) a.
    Definition to_associational n (a : tuple (F q) n) : list (F q * nat) :=
      to_list n (Tuple.map2 pair a (Tuple.seq 0 n)).
    Definition from_associational' n a start : tuple (F q) n :=
      List.fold_right (fun xi => Tuple.update_nth (snd xi) (F.add (fst xi))) start a.
    Definition from_associational n (a : list (F q * nat)) : tuple (F q) n :=
      from_associational' n a (repeat 0%F n).

    Lemma assoc_mul_nil_l x : assoc_mul nil x = nil.
    Proof. reflexivity. Qed.
    Lemma assoc_mul_nil_r x : assoc_mul x nil = nil.
    Proof. cbv [assoc_mul]; induction x; auto. Qed.
    Lemma assoc_mul_cons_l x0 x y : assoc_mul (x0 :: x) y = multerm y x0 ++ assoc_mul x y.
    Proof. reflexivity. Qed.
    Hint Rewrite assoc_mul_nil_l assoc_mul_nil_r assoc_mul_cons_l : push_assoc_mul.
    Hint Rewrite app_nil_l app_nil_r : push_app.
    Lemma assoc_mul_app_distr_r x y z : assoc_mul (x ++ y) z = assoc_mul x z ++ assoc_mul y z.
    Proof.
      induction x; autorewrite with push_app push_assoc_mul; [ reflexivity | ].
      rewrite IHx; apply app_assoc.
    Qed.
    Hint Rewrite assoc_mul_app_distr_r : push_assoc_mul.

    Lemma multerm_nil_l x : multerm nil x = nil.
    Proof. reflexivity. Qed.
    Lemma multerm_cons_l x0 x a :
      multerm (x0 :: x) a = ((fst a * fst x0)%F, (snd a + snd x0)%nat) :: multerm x a.
    Proof. reflexivity. Qed.
    Hint Rewrite multerm_nil_l multerm_cons_l : push_assoc_mul.
    Lemma multerm_app_distr x y a : multerm (x ++ y) a = multerm x a ++ multerm y a.
    Proof.
      induction x; autorewrite with push_app push_assoc_mul; [ reflexivity | ].
      rewrite IHx; reflexivity.
    Qed.
    Hint Rewrite  multerm_app_distr : push_assoc_mul.

    Lemma multerm_assoc z a b:
      multerm (multerm z a) b = multerm z ((fst b * fst a)%F, (snd b + snd a)%nat).
    Proof.
      induction z; [ reflexivity | ]; autorewrite with push_assoc_mul cancel_pair.
      rewrite IHz, !associative, Nat.add_assoc.
      reflexivity.
    Qed.

    Lemma multerm_assoc_mul_assoc a y z :
      multerm (assoc_mul y z) a = assoc_mul (multerm y a) z.
    Proof.
      induction y; autorewrite with push_assoc_mul; [ reflexivity | ].
      rewrite IHy, multerm_assoc. reflexivity.
    Qed.

    Ltac inversion_In :=
      repeat match goal with
             | _ => progress cbn [In] in *
             | H : _ |- _ => rewrite in_app_iff in H; cbn [In] in H
             | H : _ \/ _ |- _ => destruct H
             end.

    Lemma multerm_0 a x y :
      fst a = 0%F ->
      In y (multerm x a) -> fst y = 0%F.
    Proof.
      induction x; destruct a; intros;
        repeat match goal with
               | _ => progress subst
               | _ => progress inversion_In
               | _ => progress autorewrite with push_assoc_mul cancel_pair in *
               | _ => solve [auto]
               | _ => contradiction
               end.
    Qed.

    Lemma assoc_mul_assoc x y z :
      assoc_mul x (assoc_mul y z) = assoc_mul (assoc_mul x y) z.
    Proof.
      induction x; autorewrite with push_assoc_mul; [ reflexivity | ].
      rewrite IHx, multerm_assoc_mul_assoc.
      reflexivity.
    Qed.

    Hint Rewrite @Tuple.seq_S'
         @Tuple.map2_left_append
         @Tuple.to_list_left_append
         @Tuple.repeat_left_append : pull_left_append.

    Lemma to_associational_left_append m x x0 :
      to_associational (S m) (left_append x0 x) = (to_associational m x) ++ ((x0, m) :: nil).
    Proof.
      cbv [to_associational].
      autorewrite with pull_left_append natsimplify.
      reflexivity.
    Qed.
    Hint Rewrite to_associational_left_append : pull_left_append.

    Lemma from_associational_0 x : from_associational 0 x = tt.
    Proof. destruct (from_associational 0 x); reflexivity. Qed.
    Hint Rewrite from_associational_0 : push_from_associational.

    Lemma to_associational_zeroes m xi :
      In xi (to_associational m (repeat 0%F m)) ->
      fst xi = 0%F.
    Proof.
      induction m; intros;
        repeat match goal with
               | _ => progress subst
               | _ => progress inversion_In
               | _ => progress autorewrite with push_assoc_mul pull_left_append in *
               | _ => solve [auto]
               | _ => contradiction
               end.
    Qed.

    Lemma assoc_mul_zeroes x y xyi :
      (forall xi, In xi x -> fst xi = 0%F) ->
      In xyi (assoc_mul x y) ->
      fst xyi = 0%F.
    Proof.
      induction x; intros;
        repeat match goal with
               | _ => progress inversion_In
               | _ => progress autorewrite with push_assoc_mul in *
               | _ => solve [eauto using in_cons, multerm_0]
               | _ => contradiction
               end.
    Qed.

    Lemma update_nth_add_zeroes m i :
      Tuple.update_nth i (@F.add q 0) (repeat 0%F m) = repeat 0%F m.
    Proof.
      cbv [Tuple.update_nth]. Tuple.to_default (@F.zero q).
      rewrite update_nth_id_eq by (intros; rewrite left_identity; reflexivity).
      apply Tuple.from_list_default_to_list.
    Qed.

    Lemma mul_zeroes m x :
      (forall xi, In xi x -> fst xi = 0%F) ->
      forall y,
      from_associational m (assoc_mul x y) = repeat 0%F m.
    Proof.
      intros. cbv [from_associational from_associational'].
      apply fold_right_invariant; [ reflexivity | ].
      intros; subst.
      erewrite assoc_mul_zeroes by eassumption.
      apply update_nth_add_zeroes.
    Qed.

    Lemma from_associational_app m x y :
      from_associational m (x ++ y) = from_associational' m x (from_associational m y).
    Proof. apply fold_right_app. Qed.
    Hint Rewrite from_associational_app : push_from_associational.

    Lemma update_nth_add_comm m a b i j (x : tuple (F q) m) :
      Tuple.update_nth i (F.add a) (Tuple.update_nth j (@F.add q b) x) =
      Tuple.update_nth j (F.add b) (Tuple.update_nth i (@F.add q a) x).
    Proof.
      cbv [Tuple.update_nth]. Tuple.to_default (@F.zero q).
      rewrite !Tuple.to_list_from_list_default by distr_length.
      rewrite update_nth_update_nth_comm by (intros; rewrite !associative, (commutative a b); reflexivity).
      reflexivity.
    Qed.

    Lemma from_associational'_update_nth_comm m i x : forall a start,
      from_associational' m x (Tuple.update_nth i (F.add a) start) =
      Tuple.update_nth i (F.add a) (from_associational' m x start).
    Proof.
      cbv [from_associational'].
      induction x; autorewrite with push_assoc_mul push_fold_right cancel_pair; [ reflexivity | ].
      intros. cbn. rewrite IHx.
      rewrite update_nth_add_comm.
      reflexivity.
    Qed.
    Hint Rewrite from_associational'_update_nth_comm : push_from_associational.

    Lemma from_associational'_cons m x0 x start :
      from_associational' m (x0 :: x) start = Tuple.update_nth (snd x0) (F.add (fst x0)) (from_associational' m x start).
    Proof. cbv [from_associational']; rewrite fold_right_cons; reflexivity. Qed.
    Hint Rewrite from_associational'_cons : push_from_associational.

    Lemma multerm_add m x a b i start :
      from_associational' m (multerm x ((a + b)%F, i)) start
      = from_associational' m (multerm x (a, i)) (from_associational' m (multerm x (b, i)) start).
    Proof.
      induction x; autorewrite with push_assoc_mul push_from_associational cancel_pair; [ reflexivity | ].
      rewrite IHx; clear IHx.
      rewrite Tuple.update_nth_update_nth_eq by apply 0%F.
      apply Tuple.update_nth_ext; [ apply 0%F | ].
      intros; rewrite right_distributive, associative.
      reflexivity.
    Qed.
    Hint Rewrite multerm_add : push_from_associational.

    Lemma nth_default_to_associational d m :
      forall x i,
      List.nth_default (d, i) (to_associational m x) i = (nth_default d i x, i).
    Proof.
      intros. cbv [to_associational].
      rewrite <-to_list_map2.
      rewrite nth_default_map2 with (d1:=d) (d2:=i).
      distr_length. break_match.
      { rewrite <-!Tuple.nth_default_to_list.
        rewrite Tuple.nth_default_seq by lia.
        f_equal; omega. }
      { rewrite Tuple.nth_default_out_of_bounds by lia.
        reflexivity. }
    Qed.

    Lemma from_associational'_comm m x :
      forall y start,
      from_associational' m x (from_associational' m y start) =
      from_associational' m y (from_associational' m x start).
    Proof.
      induction x; intros; autorewrite with push_from_associational; reflexivity || congruence.
    Qed.

    Lemma to_associational_update_nth m f :
      forall i x,
      (i < m)%nat ->
      to_associational m (Tuple.update_nth i f x) =
      splice_nth i (f (nth_default 0%F i x), i) (to_associational m x).
    Proof.
      intros. cbv [to_associational Tuple.update_nth].
      Tuple.to_default (@F.zero q).
      rewrite <-!to_list_map2. cbv [Tuple.on_tuple_default].
      rewrite Tuple.to_list_from_list_default by distr_length.
      rewrite <-splice_nth_equiv_update_nth_update with (d:=0%F) by distr_length.
      rewrite (splice_nth_nth_default 0%nat (to_list m (Tuple.seq 0 m)) i) at 1 by distr_length.
      cbv [splice_nth]. rewrite map2_app, map2_cons by distr_length.
      rewrite <-firstn_map2, <-skipn_map2, <-!Tuple.nth_default_to_list.
      rewrite Tuple.nth_default_seq by lia.
      reflexivity.
    Qed.

    Lemma multerm_out_of_bounds m x a start:
      (m <= snd a)%nat ->
      from_associational' m (multerm x a) start = start.
    Proof.
      cbv [from_associational']; induction x; intros; [ reflexivity | ].
      autorewrite with push_assoc_mul push_fold_right cancel_pair.
      rewrite Tuple.update_nth_out_of_bounds by (apply 0%F || omega).
      auto.
    Qed.

    Lemma from_associational_assoc_mul_cons_r m x y0 y :
      from_associational m (assoc_mul x (y0 :: y)) = from_associational m (multerm x y0 ++ assoc_mul x y).
    Proof.
      induction x; intros;
      autorewrite with push_assoc_mul push_from_associational cancel_pair; try reflexivity; [ ].
      rewrite IHx. autorewrite with push_from_associational.
      cbv [from_associational]. rewrite Nat.add_comm.
      rewrite from_associational'_comm with (x := multerm y _).
      apply Tuple.update_nth_ext; [ apply 0%F | ].
      intros; apply f_equal2; auto; apply commutative.
    Qed.
    Hint Rewrite from_associational_assoc_mul_cons_r : push_from_associational.

    Lemma from_associational_assoc_mul_comm m x : forall y,
      from_associational m (assoc_mul x y) = from_associational m (assoc_mul y x).
    Proof.
      induction x; intros; autorewrite with push_assoc_mul push_from_associational;
        reflexivity || congruence.
    Qed.

    Lemma from_associational_cons m x0 x :
      from_associational m (x0 :: x) =  Tuple.update_nth (snd x0) (F.add (fst x0)) (from_associational m x).
    Proof. apply from_associational'_cons. Qed.
    Lemma from_associational_nil m : from_associational m nil = repeat 0%F m.
    Proof. reflexivity. Qed.
    Hint Rewrite from_associational_cons from_associational_nil : push_from_associational.

    Lemma assoc_mul_trim_high_l m x y:
      from_associational m (assoc_mul (to_associational m (from_associational m x)) y) = from_associational m (assoc_mul x y).
    Proof.
      induction x as [|[x0 i] ?]; intros;
        autorewrite with push_assoc_mul push_from_associational cancel_pair.
      { rewrite mul_zeroes; eauto using to_associational_zeroes. }
      { destruct (dec (i < m)%nat).
        { rewrite <-IHx. clear IHx.
          rewrite to_associational_update_nth by omega.
          rewrite (splice_nth_nth_default (0%F, i) (to_associational _ (from_associational _ x)) i) at 2 by (subst; cbv [to_associational]; distr_length).
          cbv [splice_nth].
          rewrite !assoc_mul_app_distr_r.
          autorewrite with push_assoc_mul push_from_associational.
          rewrite nth_default_to_associational.
          apply from_associational'_comm. }
        { rewrite Tuple.update_nth_out_of_bounds by (apply 0%F || omega).
          rewrite multerm_out_of_bounds by (autorewrite with cancel_pair; omega).
          apply IHx. } }
    Qed.
    Lemma assoc_mul_trim_high_r m x y:
      from_associational m (assoc_mul x (to_associational m (from_associational m y))) = from_associational m (assoc_mul x y).
    Proof.
      rewrite from_associational_assoc_mul_comm. rewrite assoc_mul_trim_high_l.
      apply from_associational_assoc_mul_comm.
    Qed.

    Lemma one_left_append m :
      (0 < m)%nat ->
      Tuple.update_nth 0%nat (fun _ : F q => 1%F) (repeat 0%F (S m)) =
      left_append 0%F (Tuple.update_nth 0%nat (fun _ => 1%F) (repeat 0%F m)).
    Proof.
      induction m; intros; [ omega | ].
      cbn [repeat].
      rewrite !Tuple.update_nth_append_eq.
      rewrite left_append_append.
      rewrite <-Tuple.repeat_left_append.
      reflexivity.
    Qed.

    Lemma from_associational_app' m x y :
      from_associational m (x ++ y) = from_associational' m y (from_associational m x).
    Proof.
      rewrite from_associational_app.
      cbv [from_associational]; auto using from_associational'_comm.
    Qed.

    Lemma from_associational'_left_append m x :
      forall start start0,
      (forall xi, In xi x -> (snd xi < m)%nat) ->
      (from_associational' (S m) x (left_append start0 start)) = left_append start0 (from_associational' m x start).
    Proof.
      induction x; intros ? ? Hin; [ reflexivity | ].
      rewrite !from_associational'_cons.
      rewrite <-!from_associational'_update_nth_comm.
      rewrite Tuple.update_nth_left_append_neq by auto using in_eq.
      rewrite IHx by auto using in_cons.
      reflexivity.
    Qed.

    Lemma from_associational_left_append m x :
      (forall xi, In xi x -> (snd xi < m)%nat) ->
      (from_associational (S m) x) = left_append 0%F (from_associational m x).
    Proof.
      cbv [from_associational]. intros.
      rewrite Tuple.repeat_left_append.
      auto using from_associational'_left_append.
    Qed.

    Lemma to_associational_index_upper_bound m x :
      forall xi,
        In xi (to_associational m x) -> (snd xi < m)%nat.
    Proof.
      induction m; [destruct x; contradiction | ].
      intros until 0. intro Hin.
      rewrite (subst_left_append x), to_associational_left_append in Hin.
      apply in_app_or in Hin; destruct Hin as [? | [? | ?] ].
      { eauto using Nat.lt_lt_succ_r. }
      { subst; cbn; omega. }
      { contradiction. }
    Qed.

    Lemma from_associational'_nil m start :
      from_associational' m nil start = start.
    Proof. cbv [from_associational']; autorewrite with push_fold_right; reflexivity. Qed.

    Lemma from_associational_to_associational m x :
      from_associational m (to_associational m x) = x.
    Proof.
      cbv [to_associational];
        induction m; [ destruct x; reflexivity | ].
      rewrite Tuple.seq_S'.
      rewrite (subst_left_append x).
      rewrite Tuple.map2_left_append.
      rewrite Tuple.to_list_left_append.
      rewrite from_associational_app'.
      rewrite from_associational_left_append by apply to_associational_index_upper_bound.
      rewrite IHm.
      rewrite from_associational'_cons.
      rewrite from_associational'_nil.
      autorewrite with cancel_pair.
      rewrite Tuple.update_nth_left_append_eq.
      rewrite right_identity; reflexivity.
    Qed.

    Lemma assoc_mul_one_r m x:
      from_associational m (assoc_mul x ((1%F, 0%nat) :: nil)) = from_associational m x.
    Proof.
      induction x; [ reflexivity | ].
      autorewrite with push_assoc_mul push_app cancel_pair.
      cbv [from_associational] in *; rewrite !from_associational'_cons.
      rewrite right_identity.
      autorewrite with cancel_pair natsimplify.
      rewrite IHx. reflexivity.
    Qed.

    Lemma add_from_associational :
      forall a b m,
      map2 F.add (from_associational m a) (from_associational m b) = from_associational m (a ++ b).
    Proof.
      cbv [from_associational]; induction a; intros.
      { rewrite from_associational'_nil, app_nil_l.
        rewrite Tuple.map2_zeroes_l by apply left_identity.
        reflexivity. }
      { rewrite <-app_comm_cons.
        rewrite !from_associational'_cons.
        rewrite Tuple.map2_update_nth_comm by (try apply 0%F; intros; rewrite associative; reflexivity).
        rewrite IHa. reflexivity. }
    Qed.

    Lemma multerm_add_distr m b c:
      forall n a,
      from_associational n (multerm (to_associational m (map2 F.add b c)) a)
      = from_associational n (multerm (to_associational m b) a ++ multerm (to_associational m c) a).
    Proof.
      induction m; intros; [ reflexivity | ].
      rewrite (subst_left_append b), (subst_left_append c).
      rewrite Tuple.map2_left_append.
      rewrite !to_associational_left_append.
      rewrite !multerm_app_distr.
      rewrite from_associational_app'.
      rewrite IHm.
      rewrite <-app_assoc.
      rewrite !from_associational_app.
      cbv [from_associational].
      autorewrite with push_assoc_mul cancel_pair push_app.
      rewrite !from_associational'_cons, !from_associational'_nil.
      autorewrite with cancel_pair.
      rewrite !from_associational'_update_nth_comm.
      rewrite Tuple.update_nth_update_nth_eq by apply 0%F.
      apply Tuple.update_nth_ext; [ apply 0%F | ].
      intros. rewrite left_distributive, associative.
      reflexivity.
    Qed.

    Lemma assoc_mul_add_distr_l m a b c:
      from_associational m (assoc_mul a (to_associational m (map2 F.add b c))) =
      map2 F.add (from_associational m (assoc_mul a (to_associational m b))) (from_associational m (assoc_mul a (to_associational m c))).
    Proof.
      induction a; intros; autorewrite with push_assoc_mul.
      { cbn. rewrite Tuple.map2_zeroes_l by apply left_identity. reflexivity. }
      { rewrite from_associational_app.
        rewrite IHa.
        rewrite !add_from_associational.
        rewrite <-app_assoc.
        rewrite !from_associational_app.
        cbv [from_associational];
          rewrite !from_associational'_comm with (x:=multerm _ _) (y:=assoc_mul _ _).
        fold (from_associational m (multerm (to_associational m (map2 F.add b c)) a)).
        rewrite multerm_add_distr. rewrite from_associational_app.
        reflexivity. }
    Qed.
  End associational.
End Lists.

(* TODO : use associational idea *)
Module PolynomialRing.
  Section PolynomialRing.
    Context {n : nat} {q : BinNums.positive}.

    Definition Rq : Type := tuple (F q) n.

    Definition zero : Rq := repeat 0%F n.
    Definition one : Rq := (Lists.from_associational n ((1%F, 0%nat) :: nil)).
    Definition opp : Rq -> Rq := map F.opp.
    Definition add : Rq -> Rq -> Rq := map2 F.add.
    Definition sub : Rq -> Rq -> Rq := fun p q => add p (opp q).
    Definition mul : Rq -> Rq -> Rq :=
      fun p q => Lists.from_associational
                   n (Lists.assoc_mul (Lists.to_associational n p)
                                      (Lists.to_associational n q)).

    Hint Rewrite @map_append @map2_append @Tuple.repeat_append : pull_append.
    Hint Rewrite (@associative (F q)) using (apply F.commutative_ring_modulo): fsimpl.
    Hint Rewrite (@left_identity (F q)) using (apply F.commutative_ring_modulo): fsimpl.
    Hint Rewrite (@right_identity (F q)) using (apply F.commutative_ring_modulo): fsimpl.
    Hint Rewrite (@left_inverse (F q)) using (apply F.commutative_ring_modulo): fsimpl.
    Local Ltac induct :=
      cbv [Rq zero one opp add sub mul] in *;
      Tuple.induct n.

    Lemma add_assoc x y z : add x (add y z) = add (add x y) z.
    Proof.
      induct; [ reflexivity | ].
      autorewrite with pull_append fsimpl.
      congruence.
    Qed.
    Lemma add_comm x y : add x y = add y x.
    Proof.
      induct; [ reflexivity | ].
      autorewrite with pull_append.
      f_equal; auto; apply commutative.
    Qed.
    Lemma add_zero_l x : add zero x = x.
    Proof.
      induct; [ reflexivity | ].
      autorewrite with pull_append fsimpl.
      congruence.
    Qed.
    Lemma add_zero_r x : add x zero = x.
    Proof. rewrite add_comm; apply add_zero_l. Qed.
    Lemma add_opp_l x : add (opp x) x = zero.
    Proof.
      induct; [ reflexivity | ].
      autorewrite with pull_append fsimpl.
      congruence.
    Qed.
    Lemma add_opp_r x : add x (opp x) = zero.
    Proof. rewrite add_comm; apply add_opp_l. Qed.
    Lemma mul_assoc x y z : mul x (mul y z) = mul (mul x y) z.
    Proof.
      cbv [mul].
      rewrite Lists.assoc_mul_trim_high_l, Lists.assoc_mul_trim_high_r.
      rewrite Lists.assoc_mul_assoc.
      reflexivity.
    Qed.
    Lemma mul_comm x y : mul x y = mul y x.
    Proof. apply Lists.from_associational_assoc_mul_comm. Qed.
    Lemma mul_one_r x : mul x one = x.
    Proof.
      cbv [mul one zero Rq] in *.
      rewrite Lists.assoc_mul_trim_high_r.
      Tuple.rev_induct n; [ reflexivity | ].
      rewrite Lists.to_associational_left_append.
      rewrite Lists.assoc_mul_app_distr_r, Lists.assoc_mul_cons_l, Lists.assoc_mul_nil_l.
      rewrite Lists.multerm_cons_l, Lists.multerm_nil_l.
      autorewrite with push_app cancel_pair.
      rewrite Lists.from_associational_app'.
      rewrite Lists.assoc_mul_one_r.
      rewrite Lists.from_associational'_cons, Lists.from_associational'_nil.
      autorewrite with natsimplify cancel_pair.
      rewrite Lists.from_associational_left_append by apply Lists.to_associational_index_upper_bound.
      rewrite Lists.from_associational_to_associational.
      rewrite Tuple.update_nth_left_append_eq.
      rewrite !right_identity.
      reflexivity.
    Qed.
    Lemma mul_one_l x : mul one x = x.
    Proof. rewrite mul_comm; apply mul_one_r. Qed.
    Lemma mul_add_distr_l a b c : mul a (add b c) = add (mul a b) (mul a c).
    Proof. apply Lists.assoc_mul_add_distr_l. Qed.
    Lemma mul_add_distr_r a b c : mul (add b c) a = add (mul b a) (mul c a).
    Proof. rewrite mul_comm, mul_add_distr_l, !(mul_comm a); reflexivity. Qed.

    Local Hint Resolve add_assoc add_comm add_zero_l add_zero_r add_opp_l add_opp_r mul_assoc mul_one_l mul_one_r mul_add_distr_l mul_add_distr_r.
    Lemma Rq_ring : @ring Rq eq zero one opp add sub mul.
    Proof. repeat econstructor; auto; try congruence. Qed.

    Section with_bytestream.
      Context (stream byte : Type)
              (byte0 : byte)
              (make_byte : tuple bool 8 -> byte)
              (get_bit : byte -> nat -> bool).
      Let byte_array := tuple byte.
      Let bit_array := tuple bool.
      Let nth_byte {l} (B : byte_array l) i := nth_default byte0 i B.
      Let nth_bit {l} (B : bit_array l) i := nth_default false i B.

      Definition bytes_to_bits {l} (B : byte_array l)
        : bit_array (8*l) :=
        Tuple.flat_map (fun b => map (get_bit b) (Tuple.seq 0 8)) B.
      Definition bits_to_bytes {lx8} l (B : bit_array lx8)
        : byte_array l :=
        map (fun i => make_byte
                        (map (fun j => nth_bit B (i*8+j))
                             (Tuple.seq 0 8)))
                        (Tuple.seq 0 l).

      Definition compress (d : positive) : Rq -> tuple (F (2 ^ d)) n :=
        map (fun x : F q => F.of_Z _ ((Z.shiftl (F.to_Z x) d + (q / 2)) / q)).
      Definition decompress {d : positive} : tuple (F (2 ^ d)) n -> Rq :=
        map (fun x : F (2 ^ d) => F.of_Z _ (Z.shiftr (F.to_Z x * q + 2^(d-1)) d)).

    (* Equivalent to \sum_{j=0}^{len-1} in_bits_{j} *)
      Definition sum_bits {n} start len (B : bit_array n) :=
        fold_right
          (fun j => Z.add (Z.b2z (nth_bit B (start + j))))
          0 (List.seq 0 len).

      (* Algorithm 2 *)
      (* NOTE : The output is not meant to represent the input, just
    preserve the input's randomness. *)
      Definition CBD_sample (eta : nat) (B : byte_array (64*eta)) : Rq :=
        let B' := bytes_to_bits B in
        map (fun i =>
               let a := sum_bits (2*i*eta) eta B' in
               let b := sum_bits (2*i*eta+eta) eta B' in
               F.of_Z q (a - b))
            (Tuple.seq 0 n).
    End with_bytestream.
  End PolynomialRing.
End PolynomialRing.

Module KyberSpec.
  Import PolynomialRing.
  Import Tuple.
  Section KyberSpec.
    Context (Rq Rq_NTT : Type).
    Context {Rqeq Rqzero Rqone Rqopp Rqadd Rqsub Rqmul}
            (Rqring : @ring Rq Rqeq Rqzero Rqone Rqopp Rqadd Rqsub Rqmul).
    Context {Rq_NTTeq Rq_NTTzero Rq_NTTone Rq_NTTopp Rq_NTTadd Rq_NTTsub Rq_NTTmul}
            (Rq_NTTring : @ring Rq_NTT Rq_NTTeq Rq_NTTzero Rq_NTTone Rq_NTTopp Rq_NTTadd Rq_NTTsub Rq_NTTmul).
    Context (NTT : Rq -> Rq_NTT) (NTT_inv : Rq_NTT -> Rq).

    (* Parameters about bytestreams *)
    Context (stream byte : Type)
            (byte0 : byte)
            (get_byte : stream -> nat -> byte)
            (make_byte : tuple bool 8 -> byte)
            (bytes_to_stream : forall n, tuple byte n -> stream)
            (stream_to_bytes : forall n, stream -> tuple byte n)
            (get_bit : byte -> nat -> bool).
    Context (nat_to_byte : nat -> byte).
    Let byte_array := tuple byte.
    Let bit_array := tuple bool.
    Let nth_bit {l} (B : bit_array l) i := nth_default false i B.

    (* Kyber parameters *)
    Context (parse : stream -> Rq_NTT). (* Algorithm 1 *) (* TODO *)
    Context (k eta n : nat) (q log2q : positive)
            (dt du dv : positive) (* fields into which elements are compressed *)
            (XOF : stream -> stream) (* "extendable output function" *)
            (PRF : byte_array 32 * byte -> stream) (* pseudorandom function *)
            (H : stream -> byte_array 32)
            (G : stream -> byte_array 32 * byte_array 32). (* hash function *)

    Context (CBD_sample : byte_array (64*eta) -> Rq).
    Context (NTT_of_F :tuple (F (2^log2q)) n -> Rq_NTT) (NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n).
    Context (compress : forall d, Rq -> tuple (F (2^d)) n) (decompress : forall {d}, tuple (F (2^d)) n -> Rq).
    Arguments decompress {_}.

    (* TODO : relocate? *)
    Let matrix T n m := tuple (tuple T m) n. (* n x m matrix: m columns, n rows *)
    Definition matrix_get {T n m} (d : T) (A : matrix T n m) (i j : nat) : T :=
      nth_default d j (nth_default (repeat d m) i A).
    Definition matrix_mul n m p
               (A : matrix Rq_NTT n m)
               (B : matrix Rq_NTT m p) : matrix Rq_NTT n p :=
      map (fun j =>
             map (fun i =>
                    fold_right
                      (fun k acc => Rq_NTTadd acc
                                              (Rq_NTTmul (matrix_get Rq_NTTzero A i k)
                                                         (matrix_get Rq_NTTzero B k j)))
                      Rq_NTTzero
                      (List.seq 0 m))
                 (seq 0 p))
          (seq 0 n).
    Definition matrix_transpose n m (A : matrix Rq_NTT n m) : matrix Rq_NTT m n :=
      map (fun j => map (fun i => matrix_get Rq_NTTzero A j i) (seq 0 n)) (seq 0 m).

    Definition pksize := (n / 8 * Pos.to_nat dt * k + 32)%nat.
    Definition sksize := (n / 8 * Pos.to_nat log2q * k)%nat.
    Definition ciphertextsize := (n / 8 * Pos.to_nat du * k + n / 8 * Pos.to_nat dv * 1)%nat.
    Definition msgsize := (n / 8 * Pos.to_nat 1)%nat.
    Local Hint Transparent pksize sksize ciphertextsize msgsize.
    Local Infix "||" := concat.

    Section helpers.
      Definition split_array {T} n m {nm} (* nm = n * m *)
                 (d : T) (A : tuple T nm) : tuple (tuple T n) m :=
        map (fun i => map (fun j => nth_default d (i*m+j) A)
                          (seq 0 n))
            (seq 0 m).
      Definition bits_to_Z {n} (B : bit_array n) :=
        List.fold_right
          (fun i acc => acc + Z.shiftl (Z.b2z (nth_bit B i)) (Z.of_nat i))
          0 (List.seq 0 n).
      Definition bits_to_F m {n} (B : bit_array n) :=
        F.of_Z m (bits_to_Z B).
      Definition Z_to_bits (x : Z) n : bit_array n :=
        map (fun i => Z.testbit x (Z.of_nat i)) (seq 0 n).
      Definition F_to_bits {m} (x : F m) n : bit_array n :=
        Z_to_bits (F.to_Z x) n.
      Definition polyvec_add {k} : tuple Rq k -> tuple Rq k -> tuple Rq k :=
        map2 Rqadd.
    End helpers.
    Local Arguments polyvec_add {_} _ _.
    Local Infix "+" := polyvec_add : polyvec_scope.
    Delimit Scope polyvec_scope with poly.

    Section compression.
      Definition polyvec_compress {m} d
        : tuple Rq m -> matrix (F (2^d)) m n :=
        map (compress d).
      Definition polyvec_decompress {m d}
        : matrix (F (2^d)) m n -> tuple Rq m :=
        map (decompress).
    End compression.

    Section encoding.
      Let bytes_to_bits {l} := @bytes_to_bits byte get_bit l.
      Let bits_to_bytes {l} := @bits_to_bytes byte make_byte l.

      Definition decode {l} (B : byte_array ((n/8)*Pos.to_nat l))
        : tuple (F (2^l)) n :=
        let B' := bytes_to_bits B in
        map (bits_to_F (2^l)) (split_array (Pos.to_nat l) n false B').

      Definition encode {l} (t : tuple (F (2^l)) n)
        : byte_array ((n/8) * Pos.to_nat l) :=
        bits_to_bytes _
          (flat_map (fun x => F_to_bits x (Pos.to_nat l)) t).

      Definition polyvec_decode {k l}
                 (B : byte_array ((n/8)*Pos.to_nat l*k))
        : matrix (F (2^l)) k n :=
        map decode
            (split_array ((n/8)*Pos.to_nat l) k byte0 B).
      Definition polyvec_encode {k l}
                 (A : matrix (F (2^l)) k n)
        : byte_array ((n/8)*Pos.to_nat l*k) :=
        Tuple.flat_map encode A.
    End encoding.

    Definition gen_matrix (seed : byte_array 32) (transposed : bool)
      : matrix Rq_NTT k k
      := map (fun i => map (fun j =>
                              let i := nat_to_byte i in
                              let j := nat_to_byte j in
                              let inp := if transposed
                                         then (append j (append i seed))
                                         else (append i (append j seed)) in
                              parse (XOF (bytes_to_stream _ inp)))
                           (Tuple.seq 0 k))
             (Tuple.seq 0 k).
    Definition gen_a := fun seed => gen_matrix seed false.
    Definition gen_at := fun seed => gen_matrix seed true.
    Definition getnoise (seed : byte_array 32) (nonce : nat) : Rq :=
      CBD_sample (stream_to_bytes _ (PRF (seed, nat_to_byte nonce))).

    (* Algorithm 3 *)
    (* d should be chosen uniformly at random *)
    Definition KeyGen (d : byte_array 32)
      : byte_array pksize * byte_array sksize :=
      let '(rho, sigma) := G (bytes_to_stream _ d) in (* rho = public seed, sigma = noise seed *)
      let A := gen_a rho in
      let s := map (getnoise sigma) (Tuple.seq 0 k) in
      let e := map (getnoise sigma) (Tuple.seq k k) in
      let s' := map NTT s in
      let t := (map NTT_inv (matrix_mul k k 1 A s') + e)%poly in
      let pk := polyvec_encode (polyvec_compress dt t) || rho in
      let sk := polyvec_encode (map NTT_to_F s') in
      (pk, sk).

    Definition Enc (pk : byte_array pksize)
               (coins : byte_array 32) (msg : byte_array msgsize)
      : byte_array ciphertextsize :=
      let t := polyvec_decompress (polyvec_decode (Tuple.firstn _ pk)) in
      let rho := Tuple.skipn (n / 8 * Pos.to_nat dt * k) pk in
      let At := gen_at rho in
      let r := map (getnoise coins) (Tuple.seq 0 k) in
      let e1 := map (getnoise coins) (Tuple.seq k k) in
      let e2 : tuple Rq 1 := getnoise coins (2*k)%nat in
      let r' := map NTT r in
      let u := (map NTT_inv (matrix_mul k k 1 At r') + e1)%poly in
      let t' := map NTT t in
      let tTr : tuple Rq 1 := NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k t') r') in
      let v := (tTr + e2 + (decompress (decode msg)))%poly in
      let c1 := polyvec_encode (polyvec_compress du u) in
      let c2 := polyvec_encode (polyvec_compress dv v) in
      c1 || c2.

    Definition Dec (sk : byte_array sksize)
               (c : byte_array ciphertextsize)
      : byte_array msgsize :=
      let u := polyvec_decompress (polyvec_decode (firstn _ c)) in
      let v := polyvec_decompress (polyvec_decode (skipn _ c)) in
      let s' := map NTT_of_F (polyvec_decode sk) in
      let u' := map NTT u in
      let sTu := NTT_inv (matrix_mul 1 k 1 (matrix_transpose 1 k s') u') in
      let m := encode (compress 1 (Rqsub v sTu)) in
      m.

  End KyberSpec.
End KyberSpec.

Module Bytes.
  Definition byte := tuple bool 8.
  Definition byte0 : byte := repeat false 8.
  Definition byte_array := tuple byte.
  Definition stream : Type := {n & byte_array n}.
  Definition get_bit (b : byte) (n : nat) := nth_default false n b.
  Definition get_byte (s : stream) (n : nat) := nth_default byte0 n (projT2 s).
  Definition stream_to_bytes n (s : stream) : byte_array n := map (get_byte s) (Tuple.seq 0 n).
  Definition bytes_to_stream n (b : byte_array n) : stream := existT _ n b.
  Definition nat_to_byte (n : nat) : byte := map (Nat.testbit n) (Tuple.seq 0 8).
End Bytes.

Module Kyber512.
  Import Bytes.
  Definition n := 512%nat.
  Definition k := 2%nat.
  Definition q := 7681%positive.
  Definition log2q := Eval compute in (Pos.size q).
  Definition eta := 5%nat.
  Definition du := 11%positive.
  Definition dv := 3%positive.
  Definition dt := 11%positive.

  Definition pksize := Eval compute in (KyberSpec.pksize k n dt).
  Definition sksize := Eval compute in (KyberSpec.sksize k n log2q).
  Definition ciphertextsize := Eval compute in (KyberSpec.ciphertextsize k n du dv).
  Definition msgsize := Eval compute in (KyberSpec.msgsize n).

  Axiom Rq_NTT : Type.
  Axiom Rq_NTTadd : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTmul : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTzero : Rq_NTT.
  Axiom NTT : @PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> @PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
  Axiom parse : stream -> Rq_NTT.
  Axiom XOF : stream -> stream.
  Axiom PRF : byte_array 32%nat * byte -> stream.
  Axiom G : stream -> byte_array 32%nat * byte_array 32%nat.

  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen (@PolynomialRing.Rq n q)
                         Rq_NTT
                         (@PolynomialRing.add n q)
                         Rq_NTTzero
                         Rq_NTTadd
                         Rq_NTTmul
                         NTT
                         NTT_inv
                         stream
                         byte
                         id
                         bytes_to_stream
                         stream_to_bytes
                         nat_to_byte
                         parse
                         k eta n log2q dt XOF PRF G
                         (@PolynomialRing.CBD_sample n q byte get_bit eta)
                         NTT_to_F
                         (@PolynomialRing.compress n q)
                         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc (@PolynomialRing.Rq n q)
                      Rq_NTT
                      (@PolynomialRing.add n q)
                      Rq_NTTzero
                      Rq_NTTadd
                      Rq_NTTmul
                      NTT
                      NTT_inv
                      stream
                      byte
                      byte0
                      id
                      bytes_to_stream
                      stream_to_bytes
                      get_bit
                      nat_to_byte
                      parse
                      k eta n dt du dv XOF PRF
                      (@PolynomialRing.CBD_sample n q byte get_bit eta)
                      (@PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec (@PolynomialRing.Rq n q)
                      Rq_NTT
                      (@PolynomialRing.add n q)
                      Rq_NTTzero
                      Rq_NTTadd
                      Rq_NTTmul
                      NTT
                      NTT_inv
                      byte
                      byte0
                      id
                      get_bit
                      k n log2q du dv
                      NTT_of_F
                      (@PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      sk c.
End Kyber512.

Module Kyber32.
  Import Bytes.
  Definition n := 32%nat.
  Definition k := 1%nat.
  Definition q := 5%positive.
  Definition log2q := Eval compute in (Pos.size q).
  Definition eta := 3%nat.
  Definition du := 5%positive.
  Definition dv := 1%positive.
  Definition dt := 5%positive.

  Definition pksize := Eval compute in (KyberSpec.pksize k n dt).
  Definition sksize := Eval compute in (KyberSpec.sksize k n log2q).
  Definition ciphertextsize := Eval compute in (KyberSpec.ciphertextsize k n du dv).
  Definition msgsize := Eval compute in (KyberSpec.msgsize n).

  Definition Rq_NTT := @PolynomialRing.Rq n q.
  Definition NTT (x : @PolynomialRing.Rq n q) : Rq_NTT := x.
  Definition NTT_inv (x : Rq_NTT) : @PolynomialRing.Rq n q := x.
  Definition NTT_to_F (x : Rq_NTT) : tuple (F (2^log2q)) n := map (fun y => F.of_Z _ (F.to_Z y)) x.
  Definition NTT_of_F (x : tuple (F (2^log2q)) n) : Rq_NTT := map (fun y => F.of_Z _ (F.to_Z y)) x.
  (*
  Axiom Rq_NTT : Type.
  Axiom Rq_NTTadd : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTmul : Rq_NTT -> Rq_NTT -> Rq_NTT.
  Axiom Rq_NTTzero : Rq_NTT.
  Axiom NTT : PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
   *)
  Axiom parse : stream -> Rq_NTT.
  Axiom XOF : stream -> stream.
  Axiom PRF : byte_array 32%nat * byte -> stream.
  Axiom G : stream -> byte_array 32%nat * byte_array 32%nat.

  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen (@PolynomialRing.Rq n q)
                         Rq_NTT
                         (@PolynomialRing.add n q)
                         (@PolynomialRing.zero n q)
                         (@PolynomialRing.add n q)
                         (@PolynomialRing.mul n q)
                         NTT
                         NTT_inv
                         stream
                         byte
                         id
                         bytes_to_stream
                         stream_to_bytes
                         nat_to_byte
                         parse
                         k eta n log2q dt XOF PRF G
                         (@PolynomialRing.CBD_sample n q byte get_bit eta)
                         NTT_to_F
                         (@PolynomialRing.compress n q)
                         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc (@PolynomialRing.Rq n q)
                      Rq_NTT
                      (@PolynomialRing.add n q)
                      (@PolynomialRing.zero n q)
                      (@PolynomialRing.add n q)
                      (@PolynomialRing.mul n q)
                      NTT
                      NTT_inv
                      stream
                      byte
                      byte0
                      id
                      bytes_to_stream
                      stream_to_bytes
                      get_bit
                      nat_to_byte
                      parse
                      k eta n dt du dv XOF PRF
                      (@PolynomialRing.CBD_sample n q byte get_bit eta)
                      (@PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec (@PolynomialRing.Rq n q)
                      Rq_NTT
                      (@PolynomialRing.add n q)
                      (@PolynomialRing.zero n q)
                      (@PolynomialRing.add n q)
                      (@PolynomialRing.mul n q)
                      NTT
                      NTT_inv
                      byte
                      byte0
                      id
                      get_bit
                      k n log2q du dv
                      NTT_of_F
                      (@PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      sk c.

  Local Notation "subst! v 'for' x 'in' e" := (match v with x => e end) (at level 200).
  Derive encode SuchThat
         (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
           x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
           x30 x31 x,
             (*
             subst! (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9
          , x10, x11, x12, x13, x14, x15, x16, x17, x18, x19
          , x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
          , x30, x31) for x in *)
             (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9
          , x10, x11, x12, x13, x14, x15, x16, x17, x18, x19
          , x20, x21, x22, x23, x24, x25, x26, x27, x28, x29
          , x30, x31) = x ->
               encode x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
           x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
           x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
           x30 x31 = @KyberSpec.encode byte id n 1 x) As encode_eq.
  Proof.
    intros. subst x.
    cbv - [PolynomialRing.bits_to_bytes byte Tuple.flat_map KyberSpec.F_to_bits Tuple.flat_map F id].
    cbv [Tuple.flat_map].
    rewrite <-Tuple.on_tuple_default_eq with (d:=false).
    cbn - [Z.testbit].
    cbv - [F byte] in encode.
    exact eq_refl.
  Qed.

  Local Ltac decode_simpl :=
    cbv - [map F KyberSpec.split_array PolynomialRing.bytes_to_bits get_bit KyberSpec.bits_to_F];
    cbv [PolynomialRing.bytes_to_bits Tuple.flat_map];
    rewrite <-Tuple.on_tuple_default_eq with (d:= false);
    cbv [map map' Tuple.seq List.seq from_list_default from_list_default'];
    cbn [fst snd];
    cbv [KyberSpec.split_array KyberSpec.bits_to_F];
    cbn - [F F.of_Z Z.shiftl Z.add get_bit].

  Derive decode1 SuchThat
         (forall c0 c1 c2 c3 c,
             (c0, c1, c2, c3) = c ->
             decode1 c0 c1 c2 c3 = @KyberSpec.decode byte get_bit n 1 c) As decode1_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

  Derive decode3 SuchThat
         (forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c,
             (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11) = c ->
             decode3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
             = @KyberSpec.decode byte get_bit n 3 c) As decode3_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

  Derive decode5 SuchThat
         (forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c,
             (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19) = c ->
             decode5 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19
             = @KyberSpec.decode byte get_bit n 5 c) As decode5_eq.
  Proof.
    intros. subst c.
    decode_simpl.
    autorewrite with zsimplify_fast.
    exact eq_refl.
  Qed.

    Lemma fold_right_ext {A B} f g x l :
      (forall b a, f b a = g b a) ->
      @fold_right A B f x l = fold_right g x l.
    Admitted.
  Derive matrix_mul SuchThat
         (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
                 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                 x30 x31 x
                 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
                 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
                 y30 y31 y,
             (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
              x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
              x20, x21, x22, x23, x24, x25, x26, x27, x28, x29,
              x30, x31) = x ->
             (y0, y1, y2, y3, y4, y5, y6, y7, y8, y9,
              y10, y11, y12, y13, y14, y15, y16, y17, y18, y19,
              y20, y21, y22, y23, y24, y25, y26, y27, y28, y29,
              y30, y31) = y ->
             matrix_mul
                 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
                 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                 x30 x31
                 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
                 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29
                 y30 y31 =
             @KyberSpec.matrix_mul Rq_NTT PolynomialRing.zero PolynomialRing.add PolynomialRing.mul 1 1 1 x y) As matrix_mul_eq.
  Proof.
    intros. subst x y.
    cbv [KyberSpec.matrix_mul].
    cbv [PolynomialRing.zero n repeat append].
    cbv [KyberSpec.matrix_get repeat append List.seq seq].
    cbv [from_list_default from_list_default'].
    cbv [map map'].
    cbv [fold_right].
    cbv [nth_default hd hd'].
    cbv [PolynomialRing.mul Lists.to_associational map2 on_tuple2].
    Tuple.to_default (@F.zero q, 0%nat).
    cbv [seq List.seq].
    cbv [to_list to_list' ListUtil.map2 from_list_default from_list_default'].
    cbv [Lists.assoc_mul Lists.multerm List.flat_map List.map app].
    cbn [fst snd Nat.add].
    cbv [Lists.from_associational Lists.from_associational'].
    erewrite fold_right_ext with (g := fun xi => on_tuple_default _ _).
    2 : { intros. cbv [update_nth on_tuple].
          Tuple.to_default (@F.zero q).
          reflexivity. }
    cbv [repeat append fold_right].
    cbn [fst snd].
    cbv [on_tuple_default to_list to_list' from_list_default from_list_default' ListUtil.update_nth].
    cbv [PolynomialRing.add].
    cbv [map2 on_tuple2].
    Tuple.to_default (@F.zero q).
    cbn.
    destruct (F.commutative_ring_modulo q).
    destruct commutative_ring_ring.
    destruct ring_commutative_group_add.
    destruct commutative_group_group.
    destruct group_monoid.
    destruct monoid_is_left_identity, monoid_is_right_identity.
    rewrite !left_identity. rewrite !right_identity.
    subst matrix_mul. reflexivity.
  Qed.


  Derive Dec' SuchThat
         (forall sk0 sk1 sk2 sk3 sk4 sk5 sk6 sk7 sk8 sk9 sk10 sk11
                 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
                 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 : byte,
             subst! (sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11) for sk in
             subst! (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23) for c in
               Dec' (sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11) (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23)
               = Dec sk c) As Dec'_correct.
  Proof.
    intros.
    cbv [Dec KyberSpec.Dec].
    cbv - [byte] in Dec'.
    cbv [KyberSpec.polyvec_encode].
    erewrite <-encode_eq.
    2 : {
    cbv [KyberSpec.polyvec_decode KyberSpec.polyvec_decompress].
    cbv [Nat.div Pos.to_nat du dv k n log2q Nat.divmod fst Pos.iter_op Nat.add Nat.mul].
    cbv [Pos.pow Pos.iter Pos.mul].
    cbv [KyberSpec.bits_to_F KyberSpec.bits_to_Z KyberSpec.F_to_bits KyberSpec.split_array].
    cbv [PolynomialRing.bytes_to_bits PolynomialRing.bits_to_bytes].
    cbv [PolynomialRing.Rq PolynomialRing.add PolynomialRing.mul PolynomialRing.zero].
    cbv [Tuple.skipn Tuple.firstn Tuple.seq Tuple.flat_map].
    Tuple.to_default byte0.
    cbn [seq].
    cbn [from_list_default from_list_default'].
    cbn [map map' fst snd].
    cbv [Tuple.on_tuple_default].
    remember (@to_list (F q)) as X.
    cbn - [KyberSpec.decode byte byte0 NTT NTT_of_F KyberSpec.matrix_transpose F F.of_Z KyberSpec.matrix_mul Rq_NTT repeat map2 PolynomialRing.decompress PolynomialRing.compress fold_right].
    subst X.

    cbv [NTT NTT_inv].

    erewrite <-decode1_eq by reflexivity.
    erewrite <-decode3_eq by reflexivity.
    erewrite <-decode5_eq by reflexivity.

    cbv [decode3].
    cbv [NTT_of_F].
    cbn [n map map' fst snd].
    cbv [log2q].
    rewrite !F.to_Z_of_Z.
    rewrite Z.mod_0_l by congruence.

    cbv [decode5 decode1].
    cbv [PolynomialRing.decompress].
    cbv [map2 on_tuple2].
    Tuple.to_default (@F.zero q).

    cbv [KyberSpec.matrix_transpose KyberSpec.matrix_get seq].
    unfold from_list_default at 2 3.
    cbv [List.seq from_list_default'].
    cbn [map map' fst snd].
    autorewrite with zsimplify_fast.
    rewrite !F.to_Z_of_Z.
    cbn [nth_default hd hd'].
    erewrite <-matrix_mul_eq by reflexivity.
    cbv [matrix_mul].
    cbv [to_list to_list'].
    cbv [ListUtil.map2].
    cbv [from_list_default from_list_default'].
    rewrite !(@Ring.mul_0_l (F q) _ (F.of_Z q 0%Z)) by apply F.commutative_ring_modulo.
    destruct (F.commutative_ring_modulo q).
    destruct commutative_ring_ring.
    destruct ring_commutative_group_add.
    destruct commutative_group_group.
    destruct group_monoid.
    destruct monoid_is_left_identity, monoid_is_right_identity.
    rewrite !left_identity. rewrite !right_identity.
  Abort.

End Kyber32.