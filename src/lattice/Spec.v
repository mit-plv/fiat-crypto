Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Local Open Scope Z_scope.

(* following https://pq-crystals.org/kyber/data/kyber-specification.pdf *)


(* TODO: move to ListUtil *)
Lemma length_flat_map {A B} (f : A -> list B) l n :
  (forall a, In a l -> length (f a) = n) ->
  length (flat_map f l) = (n * (length l))%nat.
Proof.
  induction l; cbn [flat_map]; intros;
    repeat match goal with
           | _ => progress autorewrite with distr_length
           | _ => rewrite Nat.mul_succ_r
           | H : _ |- _ => rewrite H by auto using in_eq, in_cons
           | _ => omega
           end.
Qed.

(* TODO: make an actual tuple-land definition *)
Module Tuple.
  Definition seq start len := from_list_default 0%nat len (seq start len).
  Program Definition flat_map {A B n m} (f : A -> tuple B m) (t : tuple A n)
    : tuple B (m * n) :=
    on_tuple (List.flat_map (fun a => to_list m (f a))) _ t.
  Next Obligation.
    apply length_flat_map.
    intros; apply length_to_list.
  Defined.
  Program Definition concat {T n m} (t1 : tuple T n) (t2 : tuple T m)
    : tuple T (n + m) :=
    on_tuple2 (@List.app T) _ t1 t2.
  Next Obligation. apply app_length. Defined.
  Program Definition firstn {T} n {m} (t : tuple T (n + m)) : tuple T n :=
    on_tuple (List.firstn n) _ t.
  Next Obligation. autorewrite with distr_length. lia. Defined.
  Program Definition skipn {T} n {m} (t : tuple T (n + m)) : tuple T m :=
    on_tuple (List.skipn n) _ t.
  Next Obligation. autorewrite with distr_length. lia. Defined.
  Program Definition update_nth {T n} i (f : T -> T) (t : tuple T n) : tuple T n :=
    on_tuple (update_nth i f) _ t.
  Next Obligation. autorewrite with distr_length. lia. Defined.

  Definition on_tuple_default {A B} d (f : list A -> list B) {n m} (xs : tuple A n) :=
    from_list_default d m (f (to_list n xs)).
  Definition firstn_fill {T} d n {m} (t : tuple T m) : tuple T n :=
    on_tuple_default d (List.firstn n) t.

  Lemma on_tuple_default_eq A B d f n m H xs :
    @on_tuple_default A B d f n m xs = on_tuple f H xs.
  Proof.
    cbv [on_tuple on_tuple_default].
    erewrite <-from_list_default_eq.
    reflexivity.
  Qed.

  (* TODO : move to ListUtil *)
  Lemma length_snoc_full {T} n x t : @length T (t ++ x :: nil) = S n -> length t = n.
  Proof. distr_length. Qed.
  Lemma from_list_snoc {A n} : forall xs a H,
    @from_list A (S n) (xs ++ a :: nil) H = left_append a (from_list n xs (length_snoc_full n a xs H)).
  Proof.
    induction n; intros.
    { inversion H. destruct xs; distr_length; reflexivity. }
    { inversion H. destruct xs; distr_length.
      rewrite <-from_list_default_eq with (d:=a), <-app_comm_cons.
      assert (length (a0 :: xs ++ a :: nil) = S (S n)) as Hpf by distr_length.
      rewrite from_list_default_eq with (pf:=Hpf).
      rewrite !from_list_cons, IHn.
      rewrite <-!from_list_default_eq with (d:=a).
      auto using left_append_append. }
  Qed.
  Lemma seq_S start len : seq start (S len) = append start (seq (S start) len).
  Proof.
    cbv [seq]. cbn [List.seq].
    assert (length (start :: List.seq (S start) len) = S len) as Hpf by distr_length.
    rewrite from_list_default_eq with (pf:=Hpf).
    rewrite from_list_cons.
    rewrite <-from_list_default_eq with (d:=0%nat).
    reflexivity.
  Qed.
  Lemma seq_S' start len : seq start (S len) = left_append (start+len)%nat (seq start len).
  Proof.
    cbv [seq]. rewrite seq_snoc.
    assert (length (List.seq start len ++ (start + len)%nat :: nil) = S len) as Hpf by distr_length.
    rewrite from_list_default_eq with (pf:=Hpf).
    rewrite from_list_snoc.
    rewrite <-from_list_default_eq with (d:=0%nat).
    reflexivity.
  Qed.
  Lemma map2_left_append n A B C (f : A -> B -> C) :
    forall (xs : tuple A n) (ys : tuple B n) (x : A) (y : B),
    map2 f (left_append x xs) (left_append y ys) = left_append (f x y) (map2 f xs ys).
  Proof.
    induction n; intros; [ | destruct n]; try reflexivity.
    rewrite subst_append with (x0:=xs), subst_append with (x0:=ys).
    rewrite !left_append_append, !map2_append.
    rewrite IHn, left_append_append.
    reflexivity.
  Qed.
  Lemma to_list_left_append A n (x : tuple A n) (a : A) :
    to_list (S n) (left_append a x) = to_list n x ++ a :: nil.
  Proof.
    induction n; intros; [ | destruct n]; try reflexivity.
    rewrite subst_append with (x0:=x).
    rewrite left_append_append, !to_list_append.
    rewrite IHn. reflexivity.
  Qed.
  Lemma nth_default_S T n (d:T) i (x : tuple T (S n)) :
    nth_default d (S i) x = nth_default d i (tl x).
  Proof. reflexivity. Qed.
  Lemma nth_default_append T n (d:T) :
    forall i (x : tuple T (S n)),
    nth_default d i x = if (Nat.eq_dec i n) then (left_hd x) else nth_default d i (left_tl x).
  Proof.
    induction n; intros; destruct i; try reflexivity.
    { cbn; rewrite hd_append; reflexivity. }
    { rewrite !nth_default_S. rewrite IHn.
      break_match; try omega.
      { destruct x; reflexivity. }
      { destruct x; cbn.
        rewrite tl_append. reflexivity. } }
  Qed.
  Lemma map_nth_default A B (f : A -> B) d fd :
    forall n i (t : tuple A n),
      (i < n)%nat ->
      nth_default fd i (map f t) = f (nth_default d i t).
  Proof.
    induction n; intros; subst; [ | destruct n]; try omega.
    { destruct i; reflexivity || omega. }
    { rewrite (subst_append t), map_append.
      destruct i; try reflexivity.
      rewrite !nth_default_S, !tl_append.
      apply IHn. omega. }
  Qed.
  Lemma nth_default_seq d len :
    forall i start,
      (i < len)%nat ->
      nth_default d i (seq start len) = (start+i)%nat.
  Proof.
    induction len; intros; [ omega | rewrite seq_S ].
    destruct i; cbn [nth_default].
    { rewrite hd_append. omega. }
    { rewrite tl_append, IHlen; omega. }
  Qed.
  Lemma repeat_left_append {T n} (x : T) : repeat x (S n) = left_append x (repeat x n).
  Proof.
    induction n; [ reflexivity | ].
    cbn [repeat].
    rewrite left_append_append.
    rewrite <-IHn.
    reflexivity.
  Qed.
  Lemma to_list_from_list_default {T n} d (xs : list T) :
    length xs = n ->
    to_list n (from_list_default d n xs) = xs.
  Proof.
    intro H.
    rewrite from_list_default_eq with (pf:=H).
    apply to_list_from_list.
  Qed.
End Tuple.

(*
(* TODO : do we want this someday? *)
Module GenericArithmetic.
  Module associational.
    Section associational.
      Context {value loc : Type}.
      Context {multerms : value * loc -> value * loc -> value * loc}.
      Context {positional : nat -> Type} {zero : forall n, positional n}.
      Context {place : value * loc -> value * nat}.
      Context {index_to_loc : nat -> loc}.
      Context {nth : forall n, positional n -> nat -> value}.
      Context {add_to_nth : forall n, nat -> value -> positional n -> positional n}.
      Arguments nth {_}.
      Arguments add_to_nth {_}.

      Definition of_positional n (x : positional n) : list (value * loc) :=
        List.map (fun i => (nth x i, index_to_loc i)) (List.seq 0 n).

      Definition to_positional n (x : list (value * loc)) : positional n :=
        List.fold_right (fun vl => add_to_nth (snd (place vl)) (fst (place vl))) (zero n) x.

      Definition add (x y : list (value * loc)) : list (value * loc) := x ++ y.

      Definition mul (x y : list (value * loc)) : list (value * loc) :=
        List.flat_map (fun t => List.map (multerms t) y) x.

      Section proofs.
        Context {T} (eval : forall n, positional n -> T).
        Context (assoc_eval : list (value * loc) -> T).
        Context (eval_to_positional : forall n x, eval n (to_positional n x) = assoc_eval x).

      
*)
    

(* TODO : PolynomialRing shouldn't rely on F directly; take in an arbitrary field *)
(* TODO : use associational idea *)
Module PolynomialRing.
  Section PolynomialRing.
    Context {n : nat} {q : BinNums.positive}.

    Section associational.
      Definition multerm (a : list (F q * nat)) (x : F q * nat) : list (F q * nat) :=
        List.map (fun y => (F.mul (fst x) (fst y), (snd x + snd y)%nat)) a.
      Definition assoc_mul (a b : list (F q * nat)) : list (F q * nat) := List.flat_map (multerm b) a.
      Definition to_associational n (a : tuple (F q) n) : list (F q * nat) :=
        to_list n (Tuple.map2 pair a (Tuple.seq 0 n)).
      Definition from_associational' n a start : tuple (F q) n :=
        List.fold_right (fun xi => Tuple.update_nth (snd xi) (F.add (fst xi))) start a.
      Definition from_associational n (a : list (F q * nat)) : tuple (F q) n :=
        from_associational' n a (repeat 0%F n).
    End associational.

    Definition Rq : Type := tuple (F q) n.

    Definition zero : Rq := repeat (F.of_Z _ 0) n.
    Definition one : Rq := (from_associational n ((1%F, 0%nat) :: nil)).
    Definition opp : Rq -> Rq := map F.opp.
    Definition add : Rq -> Rq -> Rq := map2 F.add.
    Definition sub : Rq -> Rq -> Rq := fun p q => add p (opp q).
    Definition mul : Rq -> Rq -> Rq :=
      fun p q => from_associational n (assoc_mul (to_associational n p)
                                                 (to_associational n q)).
 
    Ltac induct :=
      let N := fresh "N" in
      cbv [Rq zero one opp add sub mul] in *;
      generalize dependent n;
      intro N; induction N; intros; [ | destruct N ];
      cbn [tuple tuple'] in *;
      repeat match goal with
             | x : unit |- _ => destruct x
             | x : (_ * _)%type |- _ => destruct x
             end.
    Ltac left_induct :=
      let N := fresh "N" in
      cbv [Rq zero one opp add sub mul] in *;
      generalize dependent n;
      intro N; induction N; intros; [ | destruct N ];
      repeat match goal with
             | x : unit |- _ => destruct x
             | x : tuple _ (S _) |- _ => rewrite (subst_left_append x) in *; cbv [tuple] in x
             end.

    Lemma add_assoc x y z : add x (add y z) = add (add x y) z.
    Proof.
      induct; try reflexivity.
      { cbn. apply monoid_is_associative. }
      { rewrite !(map2_S (n:=N) (@F.add q)). (* Not sure why this doesn't happen with just map2_SIMPL *)
        f_equal; auto; apply monoid_is_associative. }
    Qed.
    Lemma add_comm x y : add x y = add y x.
    Proof.
      induct; try reflexivity.
      { cbn. eapply @commutative_group_is_commutative with (eq := @eq _);
               apply (F.commutative_ring_modulo q). }
      { rewrite !(map2_S (n:=N) (@F.add q)).
        f_equal; auto; eapply @commutative_group_is_commutative with (eq := @eq _);
          apply (F.commutative_ring_modulo q). }
    Qed.
    Lemma add_zero_l x : add zero x = x.
    Proof.
      induct; try reflexivity.
      { cbn. apply monoid_is_left_identity. }
      { cbn [repeat append].
        rewrite !(map2_S (n:=N) (@F.add q)).
        f_equal; auto; apply monoid_is_left_identity. }
    Qed.
    Lemma add_zero_r x : add x zero = x.
    Proof. rewrite add_comm; apply add_zero_l. Qed.
    Lemma add_opp_l x : add (opp x) x = zero.
    Proof.
      induct; try reflexivity.
      { cbn. apply group_is_left_inverse. }
      { cbn [repeat append]. rewrite !map_S.
        rewrite !(map2_S (n:=N) (@F.add q)).
        f_equal; auto; apply group_is_left_inverse. }
    Qed.
    Lemma add_opp_r x : add x (opp x) = zero.
    Proof. rewrite add_comm; apply add_opp_l. Qed.

    Lemma to_associational_left_append m x x0 :
      to_associational (S m) (left_append x0 x) = (to_associational m x) ++ ((x0, m) :: nil).
    Proof.
      cbv [to_associational].
      rewrite Tuple.seq_S'. autorewrite with natsimplify.
      rewrite Tuple.map2_left_append, Tuple.to_list_left_append.
      reflexivity.
    Qed.

    (*
    Lemma fold_right_commutes A B (x : list B) (f : B -> A -> A) :
          forall start x0 (Hf : forall a b0 b1, f b1 (f b0 a) = f b0 (f b1 a)),
            fold_right f start (x ++ x0 :: nil) = f x0 (fold_right f start x).
    Proof.
      induction x; intros; try reflexivity.
      autorewrite with push_fold_right.
      rewrite Hf, <-IHx with (start:=start) by assumption.
      autorewrite with push_fold_right.
      reflexivity.
    Qed.

    Lemma update_nth_add_commutes m (a : tuple (F q) m) x0 x1 i0 i1 :
      Tuple.update_nth i1 (F.add x1) (Tuple.update_nth i0 (F.add x0) a) =
      Tuple.update_nth i0 (F.add x0) (Tuple.update_nth i1 (F.add x1) a).
    Proof.
      cbv [Tuple.update_nth].
      rewrite <-!Tuple.on_tuple_default_eq with (d:=0%F).
      cbv [Tuple.on_tuple_default]. apply f_equal.
      erewrite !from_list_default_eq, !to_list_from_list.
      apply list_elementwise_eq. intro i.
      rewrite !nth_update_nth. cbv [option_map].
      destruct (nth_error (to_list m a) i); break_match; try congruence.
      rewrite !associative, (commutative x1 x0). reflexivity.
      Unshelve. all: distr_length.
    Qed.

    Lemma from_associational_snoc m x :
      forall i x0,
        from_associational m (x ++ (x0, i) :: nil) = Tuple.update_nth i (F.add x0) (from_associational m x).
    Proof.
      cbv [from_associational].
      intros; apply fold_right_commutes.
      intros; apply update_nth_add_commutes.
    Qed.

    Lemma assoc_mul_snoc x x0 y :
      assoc_mul (x ++ x0 :: nil) y = assoc_mul x y ++ multerm y x0.
    Proof.
      cbv [assoc_mul]. rewrite flat_map_app.
      cbn [flat_map]. rewrite app_nil_r.
      reflexivity.
    Qed.
    *)

    Lemma assoc_mul_nil_l x : assoc_mul nil x = nil.
    Proof. reflexivity. Qed.

    Lemma assoc_mul_nil_r x : assoc_mul x nil = nil.
    Proof. cbv [assoc_mul]; induction x; auto. Qed.

    Lemma assoc_mul_cons_l x0 x y : assoc_mul (x0 :: x) y = multerm y x0 ++ assoc_mul x y.
    Proof. reflexivity. Qed.

    Hint Rewrite assoc_mul_nil_l assoc_mul_nil_r assoc_mul_cons_l : push_assoc_mul.
    Hint Rewrite app_nil_l app_nil_r : push_app.
    Hint Rewrite <-app_comm_cons : push_app.

    Lemma assoc_mul_app_distr_r x y z : assoc_mul (x ++ y) z = assoc_mul x z ++ assoc_mul y z.
    Proof.
      induction x; autorewrite with push_app push_assoc_mul; [ reflexivity | ].
      rewrite IHx; apply app_assoc.
    Qed.

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
    Hint Rewrite assoc_mul_app_distr_r multerm_app_distr : push_assoc_mul.

    Lemma multerm_assoc z a b:
      multerm (multerm z a) b = multerm z ((fst b * fst a)%F, (snd b + snd a)%nat).
    Proof.
      induction z; [ reflexivity | ]; autorewrite with push_assoc_mul cancel_pair.
      rewrite IHz.
      rewrite !associative, Nat.add_assoc.
      reflexivity.
    Qed.

    Lemma multerm_assoc_mul_assoc a y z :
      multerm (assoc_mul y z) a = assoc_mul (multerm y a) z.
    Proof.
      induction y; autorewrite with push_assoc_mul; [ reflexivity | ].
      rewrite IHy, multerm_assoc.
      reflexivity.
    Qed.

    Lemma assoc_mul_assoc x y z :
      assoc_mul x (assoc_mul y z) = assoc_mul (assoc_mul x y) z.
    Proof.
      induction x; autorewrite with push_assoc_mul; [ reflexivity | ].
      rewrite IHx, multerm_assoc_mul_assoc.
      reflexivity.
    Qed.

    Lemma from_associational_0 x : from_associational 0 x = tt.
    Proof. destruct (from_associational 0 x); reflexivity. Qed.

    Lemma multerm_0 m x y :
      In y (multerm x (0%F, m)) -> fst y = 0%F.
    Proof.
      induction x; autorewrite with push_assoc_mul cancel_pair; [ contradiction | ].
      cbn [In]. destruct 1; subst; autorewrite with cancel_pair; auto.
    Qed.

    (* TODO 
    Lemma assoc_mul_zeroes m x y :
      In y (assoc_mul (to_associational m (repeat 0%F m)) x) ->
      fst y = 0%F.
    Proof.
      induction m; autorewrite with push_assoc_mul; [ contradiction | ].
      rewrite Tuple.repeat_left_append.
      rewrite to_associational_left_append.
      rewrite assoc_mul_app_distr_r.
      autorewrite with push_assoc_mul push_app.
      intro Hin; apply in_app_or in Hin; destruct Hin; eauto using multerm_0.
    Qed. *)

    Lemma to_associational_zeroes m xi :
      In xi (to_associational m (repeat 0%F m)) ->
      fst xi = 0%F.
    Proof.
      induction m; autorewrite with push_assoc_mul; [ contradiction | ].
      rewrite Tuple.repeat_left_append.
      rewrite to_associational_left_append.
      intro Hin; apply in_app_or in Hin; destruct Hin as [? | [? | ? ] ].
      { auto. }
      { subst; reflexivity. }
      { contradiction. }
    Qed.
    
    Lemma assoc_mul_zeroes x y xyi :
      (forall xi, In xi x -> fst xi = 0%F) ->
      In xyi (assoc_mul x y) ->
      fst xyi = 0%F.
    Proof.
      induction x as [|[? ?] x]; autorewrite with push_assoc_mul; [ contradiction | ].
      intros Hx Hin.
      apply in_app_or in Hin; destruct Hin as [ Hin | ? ]; [ | solve [auto using in_cons] ].
      specialize (Hx _ (in_eq _ _)). cbn in Hx; subst.
      eauto using multerm_0.
    Qed.

    Lemma update_nth_add_zeroes m i :
      Tuple.update_nth i (@F.add q 0) (repeat 0%F m) = repeat 0%F m.
    Proof.
      cbv [Tuple.update_nth].
      rewrite <-Tuple.on_tuple_default_eq with (d:= 0%F).
      cbv [Tuple.on_tuple_default].
      rewrite update_nth_id_eq by (intros; rewrite left_identity; reflexivity).
      assert (length (to_list m (repeat (@F.zero q) m)) = m) as Hpf by distr_length.
      rewrite from_list_default_eq with (pf:=Hpf).
      apply from_list_to_list.
    Qed.

    Lemma mul_zeroes m x :
      (forall xi, In xi x -> fst xi = 0%F) ->
      forall y,
      from_associational m (assoc_mul x y) = repeat 0%F m.
    Proof.
      intros.
      cbv [from_associational from_associational'].
      apply fold_right_invariant; [ reflexivity | ].
      intros; subst.
      erewrite assoc_mul_zeroes by eassumption.
      apply update_nth_add_zeroes.
    Qed.

    Lemma update_nth_out_of_bounds {T m} i (d:T) (f:T->T) (xs : tuple T m) :
      (m <= i)%nat ->
      Tuple.update_nth i f xs = xs.
    Proof.
      intros.
      cbv [Tuple.update_nth].
      rewrite <-Tuple.on_tuple_default_eq with (d:=d).
      cbv [Tuple.on_tuple_default].
      rewrite update_nth_out_of_bounds by distr_length.
      erewrite from_list_default_eq; auto using from_list_to_list.
      Unshelve. distr_length.
    Qed.

    Lemma from_associational_app m x y :
      from_associational m (x ++ y) = from_associational' m x (from_associational m y).
    Proof. apply fold_right_app. Qed.

    (* TODO : listutil *)
    Lemma update_nth_update_nth_eq {T} (f g:T->T) xs :
      forall i,
      update_nth i f (update_nth i g xs) = update_nth i (fun x => f (g x)) xs.
    Proof.
      induction xs; destruct i; try reflexivity.
      cbn. rewrite IHxs. reflexivity.
    Qed.
    Lemma Tuple_update_nth_update_nth_eq {T m} (d:T) (f g:T->T) (xs : tuple T m) :
      forall i,
      Tuple.update_nth i f (Tuple.update_nth i g xs) = Tuple.update_nth i (fun x => f (g x)) xs.
    Proof.
      intros; cbv [Tuple.update_nth].
      rewrite <-!Tuple.on_tuple_default_eq with (d:=d).
      cbv [Tuple.on_tuple_default].
      rewrite !Tuple.to_list_from_list_default by distr_length.
      rewrite update_nth_update_nth_eq.
      reflexivity.
    Qed.
    Lemma Tuple_update_nth_ext {T m} (d:T) f g i (xs : tuple T m) :
      (forall x, f x = g x) ->
      Tuple.update_nth i f xs = Tuple.update_nth i g xs.
    Proof.
      intros; cbv [Tuple.update_nth].
      rewrite <-!Tuple.on_tuple_default_eq with (d:=d).
      cbv [Tuple.on_tuple_default].
      erewrite update_nth_ext by eauto.
      reflexivity.
    Qed.
      
    Lemma update_nth_update_nth_comm {T} (f g:T->T) xs :
      (forall x, f (g x) = g (f x)) ->
      forall i j,
      update_nth i f (update_nth j g xs) = update_nth j g (update_nth i f xs).
    Proof.
      induction xs; intros; destruct i, j;
        repeat match goal with
               | _ => rewrite <-cons_update_nth
               | _ => rewrite update_nth_cons
               | _ => reflexivity
               | _ => congruence
               end.
      rewrite IHxs by auto. reflexivity.
    Qed.
    
    Lemma update_nth_add_comm m a b i j (x : tuple (F q) m) :
      Tuple.update_nth i (F.add a) (Tuple.update_nth j (@F.add q b) x) =
      Tuple.update_nth j (F.add b) (Tuple.update_nth i (@F.add q a) x).
    Proof.
      cbv [Tuple.update_nth].
      rewrite <-!Tuple.on_tuple_default_eq with (d:=0%F).
      cbv [Tuple.on_tuple_default].
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

    Lemma from_associational'_cons m x0 x start :
      from_associational' m (x0 :: x) start = Tuple.update_nth (snd x0) (F.add (fst x0)) (from_associational' m x start).
    Proof. cbv [from_associational']; rewrite fold_right_cons; reflexivity. Qed.

    Lemma multerm_add m x a b i start : 
      from_associational' m (multerm x ((a + b)%F, i)) start
      = from_associational' m (multerm x (a, i)) (from_associational' m (multerm x (b, i)) start).
    Proof.
      induction x; autorewrite with push_assoc_mul cancel_pair; [ reflexivity | ].
      rewrite !from_associational'_cons. autorewrite with cancel_pair.
      rewrite IHx; clear IHx.
      rewrite from_associational'_update_nth_comm.
      rewrite Tuple_update_nth_update_nth_eq by apply 0%F.
      apply Tuple_update_nth_ext; [ apply 0%F | ].
      intros.
      rewrite right_distributive, associative.
      reflexivity.
    Qed.

    Lemma Tuple_nth_default_to_list T m d :
      forall i x,
      @Tuple.nth_default T m d i x = List.nth_default d (to_list m x) i.
    Proof.
      induction m; [ destruct i; reflexivity | ].
      intros. rewrite (subst_append x) at 2.
      rewrite to_list_append.
      destruct i; [ rewrite nth_default_cons; reflexivity | ].
      rewrite nth_default_cons_S.
      rewrite <-IHm. reflexivity.
    Qed.

    Lemma Tuple_nth_default_out_of_bounds T m d :
      forall i x,
        (m <= i)%nat ->
        @Tuple.nth_default T m d i x = d.
    Proof.
      induction m; [ destruct i; reflexivity | ].
      intros. destruct i; [ omega | ].
      apply IHm. omega.
    Qed.

    Lemma nth_default_to_associational d m :
      forall x i,
      List.nth_default (d, i) (to_associational m x) i = (nth_default d i x, i).
    Proof.
      intros. cbv [to_associational].
      rewrite <-to_list_map2.
      rewrite nth_default_map2 with (d1:=d) (d2:=i).
      distr_length. break_match.
      { rewrite <-!Tuple_nth_default_to_list.
        rewrite Tuple.nth_default_seq by lia.
        f_equal; omega. }
      { rewrite Tuple_nth_default_out_of_bounds by lia.
        reflexivity. }
    Qed.

    Lemma from_associational'_comm m x :
      forall y start,
      from_associational' m x (from_associational' m y start) =
      from_associational' m y (from_associational' m x start).
    Proof.
      induction x; intros; [ reflexivity | ].
      rewrite !from_associational'_cons.
      rewrite from_associational'_update_nth_comm.
      congruence.
    Qed.

    Lemma splice_nth_nth_default {T} (d:T) x :
      forall i,
      (i < length x)%nat ->
      x = splice_nth i (List.nth_default d x i) x.
    Proof.
      cbv [splice_nth]; induction x; intros; distr_length; [ ].
      destruct i; [ reflexivity | ].
      rewrite firstn_cons, nth_default_cons_S, skipn_cons_S.
      rewrite (IHx i) at 1 by omega.
      rewrite <-app_comm_cons. reflexivity.
    Qed.

    Lemma firstn_map2 A B C (f:A->B->C) xs :
      forall i ys, firstn i (ListUtil.map2 f xs ys) = ListUtil.map2 f (firstn i xs) (firstn i ys).
    Proof.
      induction xs; destruct ys; destruct i; autorewrite with push_firstn; try reflexivity; [ ].
      rewrite !map2_cons, firstn_cons.
      rewrite IHxs. reflexivity.
    Qed.
    Lemma skipn_map2 A B C (f:A->B->C) xs :
      forall i ys, skipn i (ListUtil.map2 f xs ys) = ListUtil.map2 f (skipn i xs) (skipn i ys).
    Proof.
      induction xs; destruct ys; destruct i; autorewrite with push_skipn; try reflexivity.
      { rewrite map2_nil_r; reflexivity. }
      { rewrite !map2_cons, skipn_cons_S.
        rewrite IHxs. reflexivity. }
    Qed.

    Lemma to_associational_update_nth m f :
      forall i x,
      (i < m)%nat ->
      to_associational m (Tuple.update_nth i f x) =
      splice_nth i (f (nth_default 0%F i x), i) (to_associational m x).
    Proof.
      intros. cbv [to_associational Tuple.update_nth].
      rewrite <-Tuple.on_tuple_default_eq with (d:=0%F).
      rewrite <-!to_list_map2. cbv [Tuple.on_tuple_default].
      rewrite Tuple.to_list_from_list_default by distr_length.
      rewrite <-splice_nth_equiv_update_nth_update with (d:=0%F) by distr_length.
      rewrite (splice_nth_nth_default 0%nat (to_list m (Tuple.seq 0 m)) i) at 1 by distr_length.
      cbv [splice_nth]. rewrite map2_app, map2_cons by distr_length.
      rewrite <-firstn_map2, <-skipn_map2, <-!Tuple_nth_default_to_list.
      rewrite Tuple.nth_default_seq by lia.
      reflexivity.
    Qed.

    Lemma multerm_out_of_bounds m x a start:
      (m <= snd a)%nat ->
      from_associational' m (multerm x a) start = start.
    Proof.
      cbv [from_associational']; induction x; intros; [ reflexivity | ].
      autorewrite with push_assoc_mul push_fold_right cancel_pair.
      rewrite update_nth_out_of_bounds by (apply 0%F || omega).
      auto.
    Qed.

    Lemma from_associational_assoc_mul_cons_r m x y0 y :
      from_associational m (assoc_mul x (y0 :: y)) = from_associational m (multerm x y0 ++ assoc_mul x y).
    Proof.
      induction x; intros; autorewrite with push_assoc_mul; try reflexivity; [ ].
      rewrite !from_associational_app, !from_associational'_cons.
      autorewrite with cancel_pair. rewrite IHx.
      rewrite from_associational_app.
      rewrite from_associational'_comm with (x := multerm y _).
      rewrite Nat.add_comm.
      apply Tuple_update_nth_ext; [ apply 0%F | ].
      intros; apply f_equal2; auto; apply commutative.
    Qed.
    
    Lemma from_associational_assoc_mul_comm m x : forall y,
      from_associational m (assoc_mul x y) = from_associational m (assoc_mul y x).
    Proof.
      induction x; intros; autorewrite with push_assoc_mul; try reflexivity; [ ].
      rewrite from_associational_app.
      rewrite IHx. rewrite from_associational_assoc_mul_cons_r.
      rewrite from_associational_app. reflexivity.
    Qed.

    Lemma assoc_mul_trim_high_l m x y:
      from_associational m (assoc_mul (to_associational m (from_associational m x)) y) = from_associational m (assoc_mul x y).
    Proof.
      induction x; intros; cbn [from_associational from_associational' fold_right];
        autorewrite with push_fold_right push_assoc_mul.
      { rewrite mul_zeroes; eauto using to_associational_zeroes. }
      {
        destruct (dec (snd a < m)%nat).
        { fold (from_associational' m x (repeat 0%F m)).
          fold (from_associational m x).
          rewrite from_associational_app.
          rewrite <-IHx. clear IHx.
          rewrite to_associational_update_nth by omega.
          rewrite (splice_nth_nth_default (0%F, snd a) (to_associational _ (from_associational _ x)) (snd a)) at 2 by (subst; cbv [to_associational]; distr_length).
          cbv [splice_nth].
          rewrite !assoc_mul_app_distr_r.
          autorewrite with push_assoc_mul.
          rewrite !from_associational_app.
          rewrite multerm_add.
          rewrite nth_default_to_associational.
          autorewrite with cancel_pair.
          apply from_associational'_comm. }
        { rewrite update_nth_out_of_bounds by (apply 0%F || omega).
          rewrite from_associational_app.
          rewrite multerm_out_of_bounds by omega.
          apply IHx. } }
    Qed.
    Lemma assoc_mul_trim_high_r m x y:
      from_associational m (assoc_mul x (to_associational m (from_associational m y))) = from_associational m (assoc_mul x y).
    Proof.
      rewrite from_associational_assoc_mul_comm. rewrite assoc_mul_trim_high_l.
      apply from_associational_assoc_mul_comm.
    Qed.

    Lemma mul_assoc x y z : mul x (mul y z) = mul (mul x y) z.
    Proof.
      cbv [mul].
      rewrite assoc_mul_trim_high_l.
      rewrite assoc_mul_trim_high_r.
      rewrite assoc_mul_assoc.
      reflexivity.
    Qed.
    Lemma mul_comm x y : mul x y = mul y x.
    Proof. apply from_associational_assoc_mul_comm. Qed.

    Lemma update_nth_append_eq {T m} (f:T->T) (x : tuple T m) x0 :
      Tuple.update_nth 0%nat f (append x0 x) = append (f x0) x.
    Proof.
      cbv [Tuple.update_nth].
      rewrite <-Tuple.on_tuple_default_eq with (d:=x0).
      cbv [Tuple.on_tuple_default].
      rewrite to_list_append, update_nth_cons.
      assert (length (f x0 :: to_list m x) = S m) as Hpf by distr_length.
      rewrite from_list_default_eq with (pf:=Hpf).
      rewrite from_list_cons, from_list_to_list.
      reflexivity.
    Qed.

    Lemma one_left_append m :
      (0 < m)%nat ->
      Tuple.update_nth 0%nat (fun _ : F q => 1%F) (repeat 0%F (S m)) =
      left_append 0%F (Tuple.update_nth 0%nat (fun _ => 1%F) (repeat 0%F m)).
    Proof.
      induction m; intros; [ omega | ].
      cbn [repeat].
      rewrite !update_nth_append_eq.
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


    Lemma update_nth_app_r {T} f :
      forall (xs ys : list T) i,
        (length xs <= i)%nat ->
        update_nth i f (xs ++ ys) = xs ++ update_nth (i - length xs) f ys.
    Proof.
      intros.
      destruct (lt_dec i (length xs + length ys)).
      { destruct xs as [|x0 ?]; [ autorewrite with push_app distr_length natsimplify; reflexivity | ].
        rewrite <-!splice_nth_equiv_update_nth_update with (d:=x0) by distr_length.
        cbv [splice_nth].
        autorewrite with distr_length push_firstn push_skipn push_nth_default push_app in *.
        break_match; [ omega | ].
        rewrite Nat.sub_succ_l by omega.
        rewrite <-app_assoc. reflexivity. }
      { rewrite !ListUtil.update_nth_out_of_bounds by distr_length. reflexivity. }
    Qed.
    Lemma update_nth_app_l {T} f :
      forall (xs ys : list T) i,
        (i < length xs)%nat ->
        update_nth i f (xs ++ ys) = update_nth i f xs ++ ys.
    Proof.
      intros.
      destruct ys as [|y0 ?]; [ autorewrite with push_app; reflexivity | ].
      rewrite <-!splice_nth_equiv_update_nth_update with (d:=y0) by distr_length.
      cbv [splice_nth].
      autorewrite with push_firstn push_skipn push_nth_default.
      break_match; [ | omega].
      rewrite <-app_assoc. reflexivity.
    Qed.
    Hint Rewrite @update_nth_app_r @update_nth_app_l using distr_length : push_update_nth.
    Hint Rewrite @update_nth_cons : push_update_nth.

    Lemma Tuple_update_nth_left_append_neq {T m} (f:T->T):
      forall i x0 (xs : tuple T m),
      (i < m)%nat ->
      Tuple.update_nth i f (left_append x0 xs) = left_append x0 (Tuple.update_nth i f xs).
    Proof.
      intros; cbv [Tuple.update_nth].
      rewrite <-!Tuple.on_tuple_default_eq with (d:=x0).
      cbv [Tuple.on_tuple_default].
      rewrite Tuple.to_list_left_append.
      autorewrite with push_update_nth.
      assert (length (update_nth i f (to_list m xs) ++ x0 :: nil) = S m) as Hpf by distr_length.
      rewrite Tuple.from_list_default_eq with (pf:=Hpf).
      rewrite Tuple.from_list_snoc.
      rewrite <-Tuple.from_list_default_eq with (d:=x0).
      reflexivity.
    Qed.

    Lemma Tuple_update_nth_left_append_eq {T m} (f:T->T):
      forall x0 (xs : tuple T m),
      Tuple.update_nth m f (left_append x0 xs) = left_append (f x0) xs.
    Proof.
      intros; cbv [Tuple.update_nth].
      rewrite <-!Tuple.on_tuple_default_eq with (d:=x0).
      cbv [Tuple.on_tuple_default].
      rewrite Tuple.to_list_left_append.
      rewrite update_nth_app_r by distr_length.
      distr_length; autorewrite with natsimplify push_update_nth.
      assert (length (to_list m xs ++ f x0 :: nil) = S m) as Hpf by distr_length.
      rewrite Tuple.from_list_default_eq with (pf:=Hpf).
      rewrite Tuple.from_list_snoc, from_list_to_list.
      reflexivity.
    Qed.

    Lemma from_associational'_left_append m x :
      forall start start0,
      (forall xi, In xi x -> (snd xi < m)%nat) ->
      (from_associational' (S m) x (left_append start0 start)) = left_append start0 (from_associational' m x start).
    Proof.
      induction x; intros ? ? Hin; [ reflexivity | ].
      rewrite !from_associational'_cons.
      rewrite <-!from_associational'_update_nth_comm.
      rewrite Tuple_update_nth_left_append_neq by auto using in_eq.
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
      rewrite Tuple_update_nth_left_append_eq.
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

    Lemma mul_one_r x : mul x one = x.
    Proof.
      cbv [mul one zero Rq] in *.
      rewrite assoc_mul_trim_high_r.
      induction n.
      { destruct x; reflexivity. }
      { 
        rewrite (subst_left_append x).
        rewrite to_associational_left_append.
        autorewrite with push_assoc_mul push_app cancel_pair.
        rewrite from_associational_app'.
        rewrite assoc_mul_one_r.
        rewrite from_associational'_cons, from_associational'_nil.
        autorewrite with natsimplify cancel_pair.
        rewrite from_associational_left_append by apply to_associational_index_upper_bound.
        rewrite from_associational_to_associational.
        rewrite Tuple_update_nth_left_append_eq.
        rewrite !right_identity.
        reflexivity. } 
    Qed.
    Lemma mul_one_l x : mul one x = x.
    Proof. rewrite mul_comm; apply mul_one_r. Qed.

    Lemma map2_zeroes_l {A B m} (f:A->B->B) z x :
      (forall y, f z y = y) ->
      map2 f (repeat z m) x = x.
    Proof.
      intro left_id; induction m; [ destruct x; reflexivity | ].
      rewrite (subst_append x); cbn [repeat].
      rewrite map2_append. rewrite left_id.
      rewrite IHm; reflexivity.
    Qed.

    Hint Rewrite @map2_length : distr_length.

    Lemma map2_truncate_l {A B C} (f:A->B->C) xs ys:
      ListUtil.map2 f xs ys = ListUtil.map2 f (firstn (length ys) xs) ys.
    Proof.
    Admitted.

    Lemma map2_update_nth_comm' {A B} (f : A -> B -> A) (g : A -> A) (x0:A) (y0:B):
      (forall t s, f (g t) s = g (f t s)) ->
      forall i xs ys, ListUtil.map2 f (update_nth i g xs) ys = update_nth i g (ListUtil.map2 f xs ys).
    Proof.
      intro H; intros.
      rewrite !update_nth_equiv_splice_nth.
      break_innermost_match;
        repeat match goal with
               | _ => progress autorewrite with distr_length in *
               | H : _ |- _ => apply nth_error_error_length in H
               | _ => lia
               | _ => reflexivity
               end.
      { erewrite (splice_nth_nth_default y0 ys i) at 1 by lia.
        cbv [splice_nth].
        rewrite map2_app, map2_cons by (distr_length; lia).
        rewrite firstn_map2, skipn_map2. rewrite H.
        repeat match goal with H : _ |- _ =>
                               progress rewrite
                                        ?(nth_error_Some_nth_default _ x0),
                                        ?(nth_error_Some_nth_default _ y0)
                                 in H by (distr_length; lia) end.
        Option.inversion_option; subst.
        rewrite nth_default_map2 with (d1:=x0) (d2:=y0).
        break_match; try lia.
        reflexivity. }
      { rewrite map2_truncate_l with (xs0:=splice_nth _ _ _).
        cbv [splice_nth].
        rewrite firstn_app_inleft by (distr_length; lia).
        rewrite firstn_firstn by lia.
        rewrite <-map2_truncate_l.
        reflexivity. }
    Qed.

    Hint Rewrite @update_nth_nil : push_update_nth.
    Lemma map2_update_nth_comm {A B} (f : A -> B -> A) (g : A -> A) :
      (forall t s, f (g t) s = g (f t s)) ->
      forall i xs ys, ListUtil.map2 f (update_nth i g xs) ys = update_nth i g (ListUtil.map2 f xs ys).
    Proof.
      intros; destruct xs, ys;
        autorewrite with push_update_nth; rewrite ?map2_nil_r, ?map2_nil_l; try reflexivity.

    Lemma Tuple_map2_update_nth_comm {A B} (f : A -> B -> A) (g : A -> A) (d:A):
      (forall t s, f (g t) s = g (f t s)) ->
      forall n i (x : tuple A n) y,
        map2 f (Tuple.update_nth i g x) y = Tuple.update_nth i g (map2 f x y).
    Proof.
      intros. cbv [Tuple.update_nth map2 on_tuple on_tuple2].
      repeat rewrite <-from_list_default_eq with (d0:=d), ?to_list_from_list.
      rewrite map2_update_nth_comm. reflexivity.
    Qed.

    Lemma add_from_associational :
      forall a b m,
      map2 F.add (from_associational m a) (from_associational m b) = from_associational m (a ++ b).
    Proof.
      cbv [from_associational]; induction a; intros.
      { rewrite from_associational'_nil, app_nil_l.
        rewrite map2_zeroes_l by apply left_identity.
        reflexivity. }
      { rewrite <-app_comm_cons.
        rewrite !from_associational'_cons.
        rewrite map2_update_nth_comm by (intros; rewrite associative; reflexivity).
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
      rewrite Tuple_update_nth_update_nth_eq by apply 0%F.
      apply Tuple_update_nth_ext; [ apply 0%F | ].
      intros. rewrite left_distributive, associative.
      reflexivity.
    Qed.

    Lemma assoc_mul_add_distr_l m a b c:
      from_associational m (assoc_mul a (to_associational m (map2 F.add b c))) =
      map2 F.add (from_associational m (assoc_mul a (to_associational m b))) (from_associational m (assoc_mul a (to_associational m c))).
    Proof.
      induction a; intros; autorewrite with push_assoc_mul.
      { cbn. rewrite map2_zeroes_l by apply left_identity. reflexivity. }
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
    
    Lemma mul_add_distr_l a b c : mul a (add b c) = add (mul a b) (mul a c).
    Proof. apply assoc_mul_add_distr_l. Qed.
    Lemma mul_add_distr_r a b c : mul (add b c) a = add (mul b a) (mul c a).
    Proof. rewrite mul_comm, mul_add_distr_l, !(mul_comm a); reflexivity. Qed.

    Local Hint Resolve add_assoc add_comm add_zero_l add_zero_r add_opp_l add_opp_r mul_assoc mul_one_l mul_one_r mul_add_distr_l mul_add_distr_r.
    Lemma Rq_ring : @ring Rq eq zero one opp add sub mul.
    Proof. repeat econstructor; auto; try congruence. Qed.
    Print Assumptions Rq_ring  .

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
          0 (seq 0 len).

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
  Axiom NTT : PolynomialRing.Rq n q -> Rq_NTT.
  Axiom NTT_inv : Rq_NTT -> PolynomialRing.Rq n q.
  Axiom NTT_to_F : Rq_NTT -> tuple (F (2^log2q)) n.
  Axiom NTT_of_F : tuple (F (2^log2q)) n -> Rq_NTT.
  Axiom parse : stream -> Rq_NTT.
  Axiom XOF : stream -> stream.
  Axiom PRF : byte_array 32%nat * byte -> stream.
  Axiom G : stream -> byte_array 32%nat * byte_array 32%nat.

  Definition KeyGen (d : byte_array 32) : byte_array pksize * byte_array sksize
    := @KyberSpec.KeyGen (PolynomialRing.Rq n q)
                         Rq_NTT
                         (PolynomialRing.add n q)
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
                         (PolynomialRing.CBD_sample n q byte get_bit eta)
                         NTT_to_F
                         (PolynomialRing.compress n q)
                         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
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
                      (PolynomialRing.CBD_sample n q byte get_bit eta)
                      (PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
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
                      (PolynomialRing.compress n q)
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

  Definition Rq_NTT := PolynomialRing.Rq n q.
  Definition NTT (x : PolynomialRing.Rq n q) : Rq_NTT := x.
  Definition NTT_inv (x : Rq_NTT) : PolynomialRing.Rq n q := x.
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
    := @KyberSpec.KeyGen (PolynomialRing.Rq n q)
                         Rq_NTT
                         (PolynomialRing.add n q)
                         (PolynomialRing.zero n q)
                         (PolynomialRing.add n q)
                         (PolynomialRing.mul n q)
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
                         (PolynomialRing.CBD_sample n q byte get_bit eta)
                         NTT_to_F
                         (PolynomialRing.compress n q)
                         d.

  Definition Enc (pk : byte_array pksize) (coins : byte_array 32) (msg : byte_array msgsize)
    : byte_array ciphertextsize
    := @KyberSpec.Enc (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
                      (PolynomialRing.zero n q)
                      (PolynomialRing.add n q)
                      (PolynomialRing.mul n q)
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
                      (PolynomialRing.CBD_sample n q byte get_bit eta)
                      (PolynomialRing.compress n q)
                      (@PolynomialRing.decompress n q)
                      pk coins msg.

  Definition Dec (sk : byte_array sksize) (c : byte_array ciphertextsize) : byte_array msgsize
    := @KyberSpec.Dec (PolynomialRing.Rq n q)
                      Rq_NTT
                      (PolynomialRing.add n q)
                      (PolynomialRing.zero n q)
                      (PolynomialRing.add n q)
                      (PolynomialRing.mul n q)
                      NTT
                      NTT_inv
                      byte
                      byte0
                      id
                      get_bit
                      k n log2q du dv
                      NTT_of_F
                      (PolynomialRing.compress n q)
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
    cbv [map map' Tuple.seq seq from_list_default from_list_default'];
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
    rewrite <-!Tuple.on_tuple_default_eq with (d:=byte0).
    cbn [seq].
    cbn [from_list_default from_list_default'].
    cbn [map map' fst snd].
    cbv [Tuple.on_tuple_default].
    remember (@to_list (F q)) as X.
    cbn - [KyberSpec.decode byte byte0 NTT NTT_of_F KyberSpec.matrix_transpose F F.of_Z KyberSpec.matrix_mul Rq_NTT repeat map2 PolynomialRing.scmul PolynomialRing.decompress PolynomialRing.compress fold_right].
    subst X.

    erewrite <-decode1_eq by reflexivity.
    erewrite <-decode3_eq by reflexivity.
    erewrite <-decode5_eq by reflexivity.

    cbv [decode5 decode1].
    cbv [PolynomialRing.decompress].
    cbn - [decode3 NTT_of_F KyberSpec.matrix_transpose map2 PolynomialRing.compress Z.shiftr Z.shiftl F F.of_Z Z.b2z get_bit to_list].
    rewrite !F.to_Z_of_Z.
    autorewrite with zsimplify_fast.
    change (Z.shiftr 1 1) with 0.
    change (Z.shiftr 16 5) with 0.
 
    cbv [NTT].

    cbv [decode3].
    cbv [NTT_of_F].
    cbn [n map map' fst snd].
    cbv [log2q].
    rewrite !F.to_Z_of_Z.
    rewrite Z.mod_0_l.

    cbv [KyberSpec.matrix_transpose].
    cbv [Tuple.seq seq from_list_default from_list_default'].
    cbv [KyberSpec.matrix_get map map' nth_default hd hd'].
    cbv [to_list to_list'].
    cbv [KyberSpec.matrix_mul].
    cbv [Tuple.seq seq from_list_default from_list_default'].
    cbv [repeat append].
    cbv [KyberSpec.matrix_get map map' nth_default hd hd' to_list to_list' fold_right].

    cbv [PolynomialRing.scmul].
    unfold map at 30 31 32.
  (* TODO : it might make sense to change all the F (2 ^ l)  things to words, and change bytes also to words. *)
  Abort.
    
End Kyber32.