Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Local Open Scope Z_scope.

(* TODO : PolynomialRing shouldn't rely on F directly; take in an arbitrary field *)
Module Associational.
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
End Associational.

(* TODO : use associational idea *)
Module PolynomialRing.
  Section PolynomialRing.
    Context {n : nat} {q : BinNums.positive}.
    Definition Rq : Type := tuple (F q) n.

    Definition zero : Rq := repeat 0%F n.
    Definition one : Rq := (Associational.from_associational n ((1%F, 0%nat) :: nil)).
    Definition opp : Rq -> Rq := map F.opp.
    Definition add : Rq -> Rq -> Rq := map2 F.add.
    Definition sub : Rq -> Rq -> Rq := fun p q => add p (opp q).
    Definition mul : Rq -> Rq -> Rq :=
      fun p q => Associational.from_associational
                   n (Associational.assoc_mul (Associational.to_associational n p)
                                              (Associational.to_associational n q)).

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
      rewrite Associational.assoc_mul_trim_high_l, Associational.assoc_mul_trim_high_r.
      rewrite Associational.assoc_mul_assoc.
      reflexivity.
    Qed.
    Lemma mul_comm x y : mul x y = mul y x.
    Proof. apply Associational.from_associational_assoc_mul_comm. Qed.
    Lemma mul_one_r x : mul x one = x.
    Proof.
      cbv [mul one zero Rq] in *.
      rewrite Associational.assoc_mul_trim_high_r.
      Tuple.rev_induct n; [ reflexivity | ].
      rewrite Associational.to_associational_left_append.
      rewrite Associational.assoc_mul_app_distr_r, Associational.assoc_mul_cons_l, Associational.assoc_mul_nil_l.
      rewrite Associational.multerm_cons_l, Associational.multerm_nil_l.
      autorewrite with push_app cancel_pair.
      rewrite Associational.from_associational_app'.
      rewrite Associational.assoc_mul_one_r.
      rewrite Associational.from_associational'_cons, Associational.from_associational'_nil.
      autorewrite with natsimplify cancel_pair.
      rewrite Associational.from_associational_left_append by apply Associational.to_associational_index_upper_bound.
      rewrite Associational.from_associational_to_associational.
      rewrite Tuple.update_nth_left_append_eq.
      rewrite !right_identity.
      reflexivity.
    Qed.
    Lemma mul_one_l x : mul one x = x.
    Proof. rewrite mul_comm; apply mul_one_r. Qed.
    Lemma mul_add_distr_l a b c : mul a (add b c) = add (mul a b) (mul a c).
    Proof. apply Associational.assoc_mul_add_distr_l. Qed.
    Lemma mul_add_distr_r a b c : mul (add b c) a = add (mul b a) (mul c a).
    Proof. rewrite mul_comm, mul_add_distr_l, !(mul_comm a); reflexivity. Qed.

    Local Hint Resolve add_assoc add_comm add_zero_l add_zero_r add_opp_l add_opp_r mul_assoc mul_one_l mul_one_r mul_add_distr_l mul_add_distr_r.
    Lemma Rq_ring : @ring Rq eq zero one opp add sub mul.
    Proof. repeat econstructor; auto; try congruence. Qed.
  End PolynomialRing.
End PolynomialRing.

