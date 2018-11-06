Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Local Open Scope Z_scope.

Create HintDb push_from_associational discriminated.
Create HintDb push_to_associational discriminated.
Create HintDb coeffsimpl discriminated.
Create HintDb locsimpl discriminated.
Create HintDb push_mul discriminated.

(* TODO : ListUtil *)
Hint Rewrite @ListUtil.nth_default_out_of_bounds using solve [distr_length] : push_nth_default.

Class weighted_mul_preconditions {coeff loc : Type} :=
  { czero; cone; copp; cadd; csub; cmul;
    cring : @commutative_ring coeff eq czero cone copp cadd csub cmul;
    lop; lid;
    lmonoid : @monoid loc eq lop lid;
    lop_commutative : is_commutative (eq:=eq) (op:=lop);
    index_to_loc : nat -> loc;
    loc_to_index : coeff * loc -> coeff * nat;
    loc_to_index_zero : forall l, fst (loc_to_index (czero, l)) = czero;
    loc_to_index_eq : forall l c1 c2, snd (loc_to_index (c1, l)) = snd (loc_to_index (c2, l));
    loc_to_index_coeff_add : forall l c1 c2,
              fst (loc_to_index (cadd c1 c2, l)) =
              cadd (fst (loc_to_index (c1, l))) (fst (loc_to_index (c2, l)));
    loc_to_index_add_mono : forall c1 c2 l1 l2,
              (snd (loc_to_index (c1, l1)) <= snd (loc_to_index (c2, lop l1 l2)))%nat;
    loc_to_index_index_to_loc : forall c n, loc_to_index (c, index_to_loc n) = (c,n);
    (* TODO : simplify? *)
    loc_to_index_repeated :
             forall c l t,
               loc_to_index (cmul (fst (loc_to_index t)) c, lop (index_to_loc (snd (loc_to_index t))) l)
               = loc_to_index (cmul (fst t) c, lop (snd t) l);
  }.

Section associational.
  Context {coeff loc : Type}.
  Context {pre : @weighted_mul_preconditions coeff loc}.

  Local Instance cringi : commutative_ring := cring.
  Local Instance lmonoidi : monoid := lmonoid.
  Local Instance lop_commutativei : is_commutative := lop_commutative.

  Delimit Scope coeff_scope with coeff.
  Delimit Scope loc_scope with loc.
  Local Infix "+" := cadd : coeff_scope.
  Local Infix "*" := cmul : coeff_scope.
  Local Infix "+" := lop : loc_scope.
  Local Notation "0" := czero (at level 100) : coeff_scope.
  Local Notation "0" := lid (at level 100) : loc_scope.
  Local Open Scope coeff_scope.

  Local Definition term := (coeff * loc)%type.
  Local Definition positional (n : nat) := tuple coeff n.

  Definition to_associational {n} (a : positional n) : list term :=
    List.combine (to_list n a) (List.map index_to_loc (List.seq 0 n)).
  Definition add_to_nth {n} (xi : term) (a : positional n) :=
    let xi' := loc_to_index xi in
    Tuple.update_nth (snd xi') (cadd (fst xi')) a.
  Definition from_associational' n a start : tuple coeff n :=
    List.fold_right add_to_nth start a.
  Definition from_associational n (a : list term) : positional n :=
    from_associational' n a (repeat czero n).

  Definition zero (n : nat) : positional n := repeat 0 n.
  Definition one (n : nat) : positional n := add_to_nth (cone, index_to_loc 0) (zero n).
  Definition multerm (a : list term) (x : term) : list term :=
    List.map (fun y => ((fst x * fst y)%coeff, (snd x + snd y)%loc)) a.
  Definition mul (a b : list term) : list term := List.flat_map (multerm b) a.

  Hint Rewrite loc_to_index_zero loc_to_index_coeff_add : coeffsimpl.
  Hint Rewrite loc_to_index_index_to_loc : locsimpl.
  Hint Rewrite
       (@associative coeff)
       (@left_identity coeff) (@right_identity coeff)
       (@left_distributive coeff) (@right_distributive coeff)
       (@Ring.mul_0_l coeff) (@Ring.mul_0_r coeff) using apply cring : coeffsimpl.
  Hint Rewrite (@left_identity loc) (@right_identity loc) (@associative loc) using apply lmonoid : locsimpl.
  Hint Resolve in_eq in_cons loc_to_index_add_mono.

  (* Simplify goals that include [List.In] *)
  Ltac inversion_In :=
    repeat match goal with
           | _ => progress cbn [In] in *
           | H : _ |- _ => rewrite in_app_iff in H; cbn [In] in H
           | H : _ \/ _ |- _ => destruct H
           | H : False |- _ => contradiction H
           end.
  (* Unfold some tuple logic inside add_to_nth *)
  Ltac simpl_add_to_nth :=
    cbv [add_to_nth Tuple.update_nth]; Tuple.to_default 0;
    rewrite ?Tuple.to_list_from_list_default by distr_length.
  (* General-purpose goal simplifier *)
  Ltac push :=
    repeat match goal with
           | _ => progress intros
           | _ => rewrite Tuple.update_nth_out_of_bounds by eauto using le_trans, 0 with omega
           | _ => rewrite Tuple.nth_default_to_list
           | _ => rewrite seq_snoc
           | _ => progress autorewrite with push_mul push_app cancel_pair in *
           | _ => progress autorewrite with push_from_associational in *
           | _ => progress autorewrite with pull_left_append push_to_associational in *
           | _ => progress autorewrite with coeffsimpl locsimpl in *
           | _ => progress autorewrite with push_fold_right push_map push_combine push_nth_default push_firstn push_skipn natsimplify in *
           | _ => progress inversion_In; subst
           | _ => solve [eauto]
           | _ => reflexivity
           | _ => congruence
           end.

  (*** Basic properties of [mul] ***)
  Lemma mul_nil_l x : mul nil x = nil.
  Proof. reflexivity. Qed.
  Lemma mul_nil_r x : mul x nil = nil.
  Proof. cbv [mul]; induction x; auto. Qed.
  Lemma mul_cons_l x0 x y : mul (x0 :: x) y = multerm y x0 ++ mul x y.
  Proof. reflexivity. Qed.
  Hint Rewrite mul_nil_l mul_nil_r mul_cons_l : push_mul.
  Hint Rewrite app_nil_l app_nil_r : push_app.
  Lemma mul_app_distr_r x y z : mul (x ++ y) z = mul x z ++ mul y z.
  Proof. induction x; push. Qed.
  Hint Rewrite mul_app_distr_r : push_mul.

  (*** Basic properties of [multerm] ***)
  Lemma multerm_nil_l x : multerm nil x = nil.
  Proof. reflexivity. Qed.
  Lemma multerm_cons_l x0 x a :
    multerm (x0 :: x) a = ((fst a * fst x0)%coeff, (snd a + snd x0)%loc) :: multerm x a.
  Proof. reflexivity. Qed.
  Hint Rewrite multerm_nil_l multerm_cons_l : push_mul.
  Lemma multerm_app_distr x y a : multerm (x ++ y) a = multerm x a ++ multerm y a.
  Proof. induction x; push. rewrite IHx; reflexivity. Qed.
  Hint Rewrite  multerm_app_distr : push_mul.
  Lemma multerm_assoc z a b:
    multerm (multerm z a) b = multerm z ((fst b * fst a)%coeff, (snd b + snd a)%loc).
  Proof. induction z; push. Qed.
  Hint Rewrite multerm_assoc : push_mul.
  Lemma multerm_out_of_bounds m x a start:
    (m <= snd (loc_to_index a))%nat ->
    from_associational' m (multerm x a) start = start.
  Proof. cbv [from_associational' add_to_nth]; induction x; destruct a; push. Qed.
  Hint Rewrite multerm_out_of_bounds using omega : push_mul.

  (*** Associativity ***)
  Lemma multerm_mul_assoc a y z :
    multerm (mul y z) a = mul (multerm y a) z.
  Proof. induction y; push. Qed.
  Lemma mul_assoc x y z :
    mul x (mul y z) = mul (mul x y) z.
  Proof. induction x; push. rewrite multerm_mul_assoc. congruence. Qed.

  (*** Properties of to_associational ***)
  Lemma to_associational_nil : to_associational (n:=O) tt = nil.
  Proof. reflexivity. Qed.
  Hint Rewrite to_associational_nil : push_to_associational.
  Lemma to_associational_left_append m (x : positional m) x0 :
    to_associational (left_append x0 x) = (to_associational x) ++ ((x0, index_to_loc m) :: nil).
  Proof. cbv [to_associational]. rewrite seq_snoc. push. Qed.
  Hint Rewrite to_associational_left_append : push_to_associational.
  Lemma nth_default_to_associational d m x i :
    List.nth_default (d, index_to_loc i) (@to_associational m x) i = (nth_default d i x, index_to_loc i).
  Proof. cbv [to_associational]; destruct (dec (i < m)%nat); rewrite nth_default_to_list; push. Qed.
  Hint Rewrite nth_default_to_associational : push_nth_default.
  Lemma to_associational_update_nth m f i x:
    (i < m)%nat ->
    @to_associational m (Tuple.update_nth i f x) =
    splice_nth i (f (nth_default 0 i x), index_to_loc i) (to_associational x).
  Proof.
    intros. cbv [to_associational]. simpl_add_to_nth.
    rewrite <-splice_nth_equiv_update_nth_update with (d:=0) by distr_length.
    rewrite (splice_nth_nth_default (index_to_loc 0) (List.map _ (List.seq 0 m)) i) at 1 by distr_length.
    cbv [splice_nth]. push.
  Qed.
  Lemma to_associational_index_upper_bound m x :
    forall xi,
      In xi (@to_associational m x) -> (snd (loc_to_index xi) < m)%nat.
  Proof. cbv [positional] in x; Tuple.rev_induct m; push; eauto using Nat.lt_lt_succ_r. Qed.
  Hint Resolve to_associational_index_upper_bound.

  (*** Properties of from_associational' ***)
  Lemma from_associational'_nil m start :
    from_associational' m nil start = start.
  Proof. cbv [from_associational']; push. Qed.
  Hint Rewrite from_associational'_nil : push_from_associational.
  Lemma from_associational'_cons m x0 x start :
    from_associational' m (x0 :: x) start = add_to_nth x0 (from_associational' m x start).
  Proof. cbv [from_associational']; rewrite fold_right_cons; reflexivity. Qed.
  Hint Rewrite from_associational'_cons : push_from_associational.
  Lemma from_associational'_app m x y start :
    from_associational' m (x ++ y) start = from_associational' m x (from_associational' m y start).
  Proof. apply fold_right_app. Qed.
  Hint Rewrite from_associational'_app : push_from_associational.
  Lemma add_to_nth_comm m ai bj (x : positional m) :
    add_to_nth ai (add_to_nth bj x) = add_to_nth bj (add_to_nth ai x).
  Proof. simpl_add_to_nth; rewrite update_nth_update_nth_comm; push; f_equal; apply commutative. Qed.
  Lemma from_associational'_add_to_nth_comm m x : forall ai start,
      from_associational' m x (add_to_nth ai start) = add_to_nth ai (from_associational' m x start).
  Proof. cbv [from_associational']; induction x; push. rewrite IHx, add_to_nth_comm. reflexivity. Qed.
  Hint Rewrite from_associational'_add_to_nth_comm : push_from_associational.
  Lemma from_associational'_comm m x :
    forall y start,
      from_associational' m x (from_associational' m y start) =
      from_associational' m y (from_associational' m x start).
  Proof. induction x; push. Qed.
  Hint Resolve from_associational'_comm.
  Lemma multerm_add m x a b i start :
    from_associational' m (multerm x (a + b, i)) start
    = from_associational' m (multerm x (a, i)) (from_associational' m (multerm x (b, i)) start).
  Proof.
    induction x; push; [ ]; rewrite IHx; clear IHx. simpl_add_to_nth.
    repeat match goal with |- context [loc_to_index (_ ?x ?y, ?i)] =>
                           rewrite <-(loc_to_index_eq i 0 (_ x y)) end.
    rewrite ListUtil.update_nth_update_nth_eq.
    f_equal. apply ListUtil.update_nth_ext; push.
  Qed.
  Hint Rewrite multerm_add : push_from_associational.
  Lemma from_associational'_left_append m x :
    forall start start0,
      (forall xi, In xi x -> (snd (loc_to_index xi) < m)%nat) ->
      (from_associational' (S m) x (left_append start0 start)) = left_append start0 (from_associational' m x start).
  Proof.
    induction x; push; [ ]. rewrite <-!from_associational'_add_to_nth_comm.
    cbv [add_to_nth]; rewrite update_nth_left_append_neq by auto.
    rewrite IHx by auto. reflexivity.
  Qed.
  Hint Rewrite from_associational'_left_append using (eauto; omega) : pull_left_append.

  (*** Properties of from_associational ***)
  Lemma from_associational_cons m x0 x :
    from_associational m (x0 :: x) =  add_to_nth x0 (from_associational m x).
  Proof. apply from_associational'_cons. Qed.
  Lemma from_associational_nil m : from_associational m nil = repeat 0 m.
  Proof. reflexivity. Qed.
  Hint Rewrite from_associational_cons from_associational_nil : push_from_associational.
  Lemma from_associational_0 x : from_associational 0 x = tt.
  Proof. destruct (from_associational 0 x); reflexivity. Qed.
  Hint Rewrite from_associational_0 : push_from_associational.
  Lemma from_associational_app m x y :
    from_associational m (x ++ y) = from_associational' m x (from_associational m y).
  Proof. apply fold_right_app. Qed.
  Hint Rewrite from_associational_app : push_from_associational.
  Lemma from_associational_app' m x y :
    from_associational m (x ++ y) = from_associational' m y (from_associational m x).
  Proof. cbv [from_associational]; push. Qed.
  Lemma from_associational_left_append m x :
    (forall xi, In xi x -> (snd (loc_to_index xi) < m)%nat) ->
    (from_associational (S m) x) = left_append 0 (from_associational m x).
  Proof. cbv [from_associational]; push. Qed.
  Hint Rewrite from_associational_left_append using omega : pull_left_append.

  Lemma from_associational_to_associational m x :
    from_associational m (to_associational x) = x.
  Proof.
    cbv [from_associational to_associational positional] in *; Tuple.rev_induct m;
      repeat match goal with
             | _ => rewrite IHm
             | _ => Tuple.from_default; rewrite from_list_snoc, from_list_to_list
             | _ => progress simpl_add_to_nth
             | _ => progress push; autorewrite with push_update_nth distr_length
             end.
  Qed.
  Lemma add_from_associational :
    forall a b m,
      map2 cadd (from_associational m a ) (from_associational m b) = from_associational m (a ++ b).
  Proof.
    cbv [from_associational]; induction a; push.
    { rewrite map2_zeroes_l by apply left_identity; reflexivity. }
    { cbv [add_to_nth]; rewrite map2_update_nth_comm by (try apply 0; push).
      rewrite IHa; push. }
  Qed.

  (*** Working with zeroes ***)
  Lemma multerm_0 a x y :
    fst a = 0 ->
    In y (multerm x a) -> fst y = 0.
  Proof. induction x; destruct a; push. Qed.
  Hint Resolve multerm_0.
  Lemma to_associational_zeroes m xi :
    In xi (to_associational (repeat 0 m)) ->
    fst xi = 0.
  Proof. induction m; [ cbv [repeat] | ]; push. Qed.
  Hint Resolve to_associational_zeroes.
  Lemma mul_zeroes x y xyi :
    (forall xi, In xi x -> fst xi = 0) ->
    In xyi (mul x y) ->
    fst xyi = 0.
  Proof. induction x; push. Qed.
  Hint Resolve mul_zeroes.
  Lemma add_to_nth_zeroes m ai (x : positional m) :
    fst ai = 0 -> add_to_nth ai x = x.
  Proof.
    simpl_add_to_nth. destruct ai; push; subst.
    rewrite update_nth_id_eq by (intros; autorewrite with coeffsimpl; reflexivity).
    apply Tuple.from_list_default_to_list.
  Qed.
  Hint Resolve add_to_nth_zeroes.
  Lemma from_associational_mul_zeroes m x :
    (forall xi, In xi x -> fst xi = 0) ->
    forall y,
      from_associational m (mul x y) = repeat 0 m.
  Proof.
    intros. cbv [from_associational from_associational'].
    apply fold_right_invariant; intros; subst; push.
  Qed.

  (*** Properties of [from_associational _ (mul _ _)] ***)
  Lemma from_associational_mul_cons_r m x y0 y :
    from_associational m (mul x (y0 :: y)) = from_associational m (multerm x y0 ++ mul x y).
  Proof.
    induction x; push; [ ]. rewrite IHx, from_associational'_comm.
    repeat (apply f_equal2; auto; try apply commutative).
  Qed.
  Hint Rewrite from_associational_mul_cons_r : push_from_associational.
  Lemma from_associational_mul_comm m x : forall y,
      from_associational m (mul x y) = from_associational m (mul y x).
  Proof. induction x; push. Qed.

  (*** Working with ones ***)
  Lemma one_left_append m :
    (O < m)%nat ->
    one (S m) = left_append 0 (one m).
  Proof.
    cbv [one zero add_to_nth]; induction m; cbn [repeat]; push; [ ].
    rewrite !update_nth_append_eq.
    rewrite left_append_append, <-repeat_left_append.
    reflexivity.
  Qed.
  Lemma mul_one_r m x:
    from_associational m (mul x ((cone, 0%loc) :: nil)) = from_associational m x.
  Proof.  cbv [from_associational]; induction x as [|[? ?] ?]; push. Qed.
  Hint Rewrite mul_one_r : push_mul.
  Lemma from_associational_mul_one m x :
    from_associational m (mul x ((cone, 0%loc) :: nil)) = from_associational m x.
  Proof. induction x; push. Qed.

  (*** Distributivity ***)
  Lemma add_to_nth_add m x y n a:
    @add_to_nth m (x + y, n) a = add_to_nth (x, n) (add_to_nth (y, n) a).
  Proof.
    cbv [add_to_nth].
    rewrite (loc_to_index_eq n x y).
    rewrite (loc_to_index_eq n (x+y) y).
    rewrite update_nth_update_nth_eq by apply 0.
    apply Tuple.update_nth_ext; try apply 0; push.
  Qed.
  Hint Rewrite add_to_nth_add : push_from_associational.
  Lemma multerm_add_distr m b c:
    forall n a,
      from_associational n (multerm (@to_associational m (map2 cadd b c)) a)
      = from_associational n (multerm (@to_associational m b) a ++ multerm (@to_associational m c) a).
  Proof.
    cbv [from_associational positional] in *; Tuple.rev_induct m; push; [ ].
    rewrite IHm. push.
  Qed.
  Lemma mul_add_distr_l m a b c:
    from_associational m (mul a (@to_associational m (map2 cadd b c))) =
    map2 cadd (from_associational m (mul a (@to_associational m b))) (from_associational m (mul a (@to_associational m c))).
  Proof.
    induction a.
    { cbn. rewrite Tuple.map2_zeroes_l by apply left_identity. reflexivity. }
    { repeat progress (try rewrite IHa; rewrite add_from_associational; push).
      cbv [from_associational];
        rewrite !from_associational'_comm with (x:=multerm _ _) (y:=mul _ _).
      fold (from_associational m (multerm (to_associational (map2 cadd b c)) a)).
      rewrite multerm_add_distr. push. }
  Qed.

  (*** Converting from associational and then back ***)
  Lemma multerm_loc_to_index m x t start :
    from_associational' m (multerm x (fst (loc_to_index t), index_to_loc (snd (loc_to_index t)))) start
    = from_associational' m (multerm x t) start.
  Proof.
    induction x; push; [ ]. rewrite IHx.
    cbv [add_to_nth]. rewrite loc_to_index_repeated. congruence.
  Qed.
  Lemma mul_trim_high_l m x y:
    from_associational m (mul (@to_associational m (from_associational m x)) y) = from_associational m (mul x y).
  Proof.
    induction x as [|x0 ?]; push; eauto using from_associational_mul_zeroes; [ ].
    destruct (dec (snd (loc_to_index x0) < m)%nat); cbv [add_to_nth]; push; [ ].
    rewrite <-IHx. clear IHx. rewrite to_associational_update_nth by omega.
    rewrite (splice_nth_nth_default (0, index_to_loc (snd (loc_to_index x0))) (to_associational (from_associational _ x)) (snd (loc_to_index x0))) at 2 by (cbv [to_associational]; distr_length; lia).
    cbv [splice_nth]; push; rewrite multerm_loc_to_index. auto.
  Qed.
  Lemma mul_trim_high_r m x y:
    from_associational m (mul x (to_associational (from_associational m y))) = from_associational m (mul x y).
  Proof.
    rewrite from_associational_mul_comm, mul_trim_high_l.
    apply from_associational_mul_comm.
  Qed.

End associational.