Require Import Coq.Lists.List.
Require Import Coq.omega.Omega Lia.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Util.NatUtil.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.Tactics.BreakMatch.
Require Export Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.

Create HintDb distr_length discriminated.
Create HintDb simpl_set_nth discriminated.
Create HintDb simpl_update_nth discriminated.
Create HintDb simpl_nth_default discriminated.
Create HintDb simpl_nth_error discriminated.
Create HintDb simpl_firstn discriminated.
Create HintDb simpl_skipn discriminated.
Create HintDb simpl_fold_right discriminated.
Create HintDb simpl_sum_firstn discriminated.
Create HintDb push_map discriminated.
Create HintDb push_flat_map discriminated.
Create HintDb push_fold_right discriminated.
Create HintDb push_partition discriminated.
Create HintDb pull_nth_error discriminated.
Create HintDb push_nth_error discriminated.
Create HintDb pull_nth_default discriminated.
Create HintDb push_nth_default discriminated.
Create HintDb pull_firstn discriminated.
Create HintDb push_firstn discriminated.
Create HintDb pull_skipn discriminated.
Create HintDb push_skipn discriminated.
Create HintDb pull_update_nth discriminated.
Create HintDb push_update_nth discriminated.
Create HintDb znonzero discriminated.

Hint Rewrite
  @app_length
  @rev_length
  @map_length
  @seq_length
  @fold_left_length
  @split_length_l
  @split_length_r
  @firstn_length
  @combine_length
  @prod_length
  : distr_length.

Hint Extern 1 => progress autorewrite with distr_length in * : distr_length.
Ltac distr_length := autorewrite with distr_length in *;
  try solve [simpl in *; omega].

Module Export List.
  Local Set Implicit Arguments.
  Import ListNotations.
  (** From the 8.6 Standard Library *)

  Section Elts.
    Variable A : Type.

    (** Results about [nth_error] *)

    Lemma nth_error_In l n (x : A) : nth_error l n = Some x -> In x l.
    Proof using Type.
      revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
      - injection 1; auto.
      - eauto.
    Qed.
  End Elts.

  Section Map.
    Variables (A : Type) (B : Type).
    Variable f : A -> B.

    Lemma map_nil : forall A B (f : A -> B), map f nil = nil.
    Proof. reflexivity. Qed.
    Lemma map_cons (x:A)(l:list A) : map f (x::l) = (f x) :: (map f l).
    Proof using Type.
      reflexivity.
    Qed.
  End Map.
  Hint Rewrite @map_cons @map_nil : push_map.

  Section FlatMap.
    Lemma flat_map_nil {A B} (f:A->list B) : List.flat_map f (@nil A) = nil.
    Proof. reflexivity. Qed.
    Lemma flat_map_cons {A B} (f:A->list B) x xs :
      (List.flat_map f (x::xs) = (f x++List.flat_map f xs))%list.
    Proof. reflexivity. Qed.
  End FlatMap.
  Hint Rewrite @flat_map_cons @flat_map_nil : push_flat_map.

  Section FoldRight.
    Context {A B} (f:B->A->A).
    Lemma fold_right_nil : forall {A B} (f:B->A->A) a,
        List.fold_right f a nil = a.
    Proof. reflexivity. Qed.
    Lemma fold_right_cons : forall a b bs,
      fold_right f a (b::bs) = f b (fold_right f a bs).
    Proof. reflexivity. Qed.
  End FoldRight.
  Hint Rewrite @fold_right_nil @fold_right_cons : simpl_fold_right push_fold_right.

  Section Partition.
    Lemma partition_nil {A} (f:A->_) : partition f nil = (nil, nil).
    Proof. reflexivity.                                         Qed.
    Lemma partition_cons {A} (f:A->_) x xs : partition f (x::xs) =
                                             if f x
                                             then (x :: (fst (partition f xs)), (snd (partition f xs)))
                                             else ((fst (partition f xs)), x :: (snd (partition f xs))).
    Proof. cbv [partition]; break_match; reflexivity.           Qed.
  End Partition.
  Hint Rewrite @partition_nil @partition_cons : push_partition.

  Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof.
   revert start. induction len as [|len IHlen]; simpl; intros.
   - rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - rewrite IHlen, <- plus_n_Sm; simpl; split.
     * intros [H|H]; subst; intuition auto with arith.
     * intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H); intuition.
  Qed.

  Section Facts.

    Variable A : Type.

    Theorem length_zero_iff_nil (l : list A):
      length l = 0 <-> l=[].
    Proof using Type.
      split; [now destruct l | now intros ->].
    Qed.
  End Facts.

  Section Repeat.

    Variable A : Type.
    Fixpoint repeat (x : A) (n: nat ) :=
      match n with
      | O => []
      | S k => x::(repeat x k)
      end.

    Theorem repeat_length x n:
      length (repeat x n) = n.
    Proof using Type.
      induction n as [| k Hrec]; simpl; rewrite ?Hrec; reflexivity.
    Qed.

    Theorem repeat_spec n x y:
      In y (repeat x n) -> y=x.
    Proof using Type.
      induction n as [|k Hrec]; simpl; destruct 1; auto.
    Qed.

  End Repeat.

  Section Cutting.

    Variable A : Type.

    Local Notation firstn := (@firstn A).

    Lemma firstn_nil n: firstn n [] = [].
    Proof using Type. induction n; now simpl. Qed.

    Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
    Proof using Type. now simpl. Qed.

    Lemma firstn_all l: firstn (length l) l = l.
    Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

    Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
    Proof using Type. induction n as [|k iHk].
           - intro l. inversion 1 as [H1|?].
             rewrite (length_zero_iff_nil l) in H1. subst. now simpl.
           - destruct l as [|x xs]; simpl.
             * now reflexivity.
             * simpl. intro H. apply Peano.le_S_n in H. f_equal. apply iHk, H.
    Qed.

    Lemma firstn_O l: firstn 0 l = [].
    Proof using Type. now simpl. Qed.

    Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
    Proof using Type.
      induction n as [|k iHk]; simpl; [auto | destruct l as [|x xs]; simpl].
      - auto with arith.
      - apply le_n_S, iHk.
    Qed.

    Lemma firstn_length_le: forall l:list A, forall n:nat,
          n <= length l -> length (firstn n l) = n.
    Proof using Type. induction l as [|x xs Hrec].
           - simpl. intros n H. apply le_n_0_eq in H. rewrite <- H. now simpl.
           - destruct n as [|n].
             * now simpl.
             * simpl. intro H. apply le_S_n in H. now rewrite (Hrec n H).
    Qed.

    Lemma firstn_app n:
      forall l1 l2,
        firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
    Proof using Type. induction n as [|k iHk]; intros l1 l2.
           - now simpl.
           - destruct l1 as [|x xs].
             * unfold List.firstn at 2, length. now rewrite 2!app_nil_l, <- minus_n_O.
             * rewrite <- app_comm_cons. simpl. f_equal. apply iHk.
    Qed.

    Lemma firstn_app_2 n:
      forall l1 l2,
        firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
    Proof using Type. induction n as [| k iHk];intros l1 l2.
           - unfold List.firstn at 2. rewrite <- plus_n_O, app_nil_r.
             rewrite firstn_app. rewrite <- minus_diag_reverse.
             unfold List.firstn at 2. rewrite app_nil_r. apply firstn_all.
           - destruct l2 as [|x xs].
             * simpl. rewrite app_nil_r. apply firstn_all2. auto with arith.
             * rewrite firstn_app. assert (H0 : (length l1 + S k - length l1) = S k).
               auto with arith.
               rewrite H0, firstn_all2; [reflexivity | auto with arith].
    Qed.

    Lemma firstn_firstn:
      forall l:list A,
      forall i j : nat,
        firstn i (firstn j l) = firstn (min i j) l.
    Proof. induction l as [|x xs Hl].
           - intros. simpl. now rewrite ?firstn_nil.
           - destruct i.
             * intro. now simpl.
             * destruct j.
             + now simpl.
             + simpl. f_equal. apply Hl.
    Qed.

  End Cutting.

End List.

Hint Rewrite @firstn_skipn : simpl_firstn.
Hint Rewrite @firstn_skipn : simpl_skipn.
Hint Rewrite @firstn_nil @firstn_cons @List.firstn_all @firstn_O @firstn_app_2 @List.firstn_firstn : push_firstn.
Hint Rewrite @firstn_nil @firstn_cons @List.firstn_all @firstn_O @firstn_app_2 @List.firstn_firstn : simpl_firstn.
Hint Rewrite @firstn_app : push_firstn.
Hint Rewrite <- @firstn_cons @firstn_app @List.firstn_firstn : pull_firstn.
Hint Rewrite @firstn_all2 @removelast_firstn @firstn_removelast using omega : push_firstn.
Hint Rewrite @firstn_all2 @removelast_firstn @firstn_removelast using omega : simpl_firstn.

Local Arguments value / _ _.
Local Arguments error / _.

Definition sum_firstn l n := fold_right Z.add 0%Z (firstn n l).

Definition sum xs := sum_firstn xs (length xs).

Fixpoint map2 {A B C} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
  match la with
  | nil => nil
  | a :: la' => match lb with
                | nil => nil
                | b :: lb' => f a b :: map2 f la' lb'
                end
  end.

(* xs[n] := f xs[n] *)
Fixpoint update_nth {T} n f (xs:list T) {struct n} :=
	match n with
	| O => match xs with
				 | nil => nil
				 | x'::xs' => f x'::xs'
				 end
	| S n' =>  match xs with
				 | nil => nil
				 | x'::xs' => x'::update_nth n' f xs'
				 end
  end.

(* xs[n] := x *)
Definition set_nth {T} n x (xs:list T)
  := update_nth n (fun _ => x) xs.

Definition splice_nth {T} n (x:T) xs := firstn n xs ++ x :: skipn (S n) xs.
Hint Unfold splice_nth.

Ltac boring :=
  simpl; intuition auto with zarith datatypes;
  repeat match goal with
           | [ H : _ |- _ ] => rewrite H; clear H
           | [ |- context[match ?pf with end] ] => solve [ case pf ]
           | _ => progress autounfold in *
           | _ => progress autorewrite with core
           | _ => progress simpl in *
           | _ => progress intuition auto with zarith datatypes
         end; eauto.

Ltac boring_list :=
  repeat match goal with
         | _ => progress boring
         | _ => progress autorewrite with distr_length simpl_nth_default simpl_update_nth simpl_set_nth simpl_nth_error in *
         end.

Lemma nth_default_cons : forall {T} (x u0 : T) us, nth_default x (u0 :: us) 0 = u0.
Proof. auto. Qed.

Hint Rewrite @nth_default_cons : simpl_nth_default.
Hint Rewrite @nth_default_cons : push_nth_default.

Lemma nth_default_cons_S : forall {A} us (u0 : A) n d,
  nth_default d (u0 :: us) (S n) = nth_default d us n.
Proof. boring. Qed.

Hint Rewrite @nth_default_cons_S : simpl_nth_default.
Hint Rewrite @nth_default_cons_S : push_nth_default.

Lemma nth_default_nil : forall {T} n (d : T), nth_default d nil n = d.
Proof. induction n; boring. Qed.

Hint Rewrite @nth_default_nil : simpl_nth_default.
Hint Rewrite @nth_default_nil : push_nth_default.

Lemma nth_error_nil_error : forall {A} n, nth_error (@nil A) n = None.
Proof. induction n; boring. Qed.

Hint Rewrite @nth_error_nil_error : simpl_nth_error.

Ltac nth_tac' :=
  intros; simpl in *; unfold error,value in *; repeat progress (match goal with
    | [  |- context[nth_error nil ?n] ] => rewrite nth_error_nil_error
    | [ H: ?x = Some _  |- context[match ?x with Some _ => ?a | None => ?a end ] ] => destruct x
    | [ H: ?x = None _  |- context[match ?x with Some _ => ?a | None => ?a end ] ] => destruct x
    | [  |- context[match ?x with Some _ => ?a | None => ?a end ] ] => destruct x
    | [  |- context[match nth_error ?xs ?i with Some _ => _ | None => _ end ] ] => case_eq (nth_error xs i); intros
    | [ |- context[(if lt_dec ?a ?b then _ else _) = _] ] => destruct (lt_dec a b)
    | [ |- context[_ = (if lt_dec ?a ?b then _ else _)] ] => destruct (lt_dec a b)
    | [ H: context[(if lt_dec ?a ?b then _ else _) = _] |- _ ] => destruct (lt_dec a b)
    | [ H: context[_ = (if lt_dec ?a ?b then _ else _)] |- _ ] => destruct (lt_dec a b)
    | [ H: _ /\ _ |- _ ] => destruct H
    | [ H: Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
    | [ H: None = Some _  |- _ ] => inversion H
    | [ H: Some _ = None |- _ ] => inversion H
    | [ |- Some _ = Some _ ] => apply f_equal
  end); eauto; try (autorewrite with list in *); try omega; eauto.
Lemma nth_error_map : forall A B (f:A->B) i xs y,
  nth_error (map f xs) i = Some y ->
  exists x, nth_error xs i = Some x /\ f x = y.
Proof.
  induction i; destruct xs; nth_tac'.
Qed.

Lemma nth_error_seq : forall i start len,
  nth_error (seq start len) i =
  if lt_dec i len
  then Some (start + i)
  else None.
  induction i as [|? IHi]; destruct len; nth_tac'; erewrite IHi; nth_tac'.
Qed.

Lemma nth_error_error_length : forall A i (xs:list A), nth_error xs i = None ->
  i >= length xs.
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac'; try match goal with H : _ |- _ => specialize (IHi _ H) end; omega.
Qed.

Lemma nth_error_value_length : forall A i (xs:list A) x, nth_error xs i = Some x ->
  i < length xs.
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac'; try match goal with H : _ |- _ => specialize (IHi _ _ H) end; omega.
Qed.

Lemma nth_error_length_error : forall A i (xs:list A),
  i >= length xs ->
  nth_error xs i = None.
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac'; rewrite IHi by omega; auto.
Qed.
Hint Resolve nth_error_length_error.
Hint Rewrite @nth_error_length_error using omega : simpl_nth_error.

Lemma map_nth_default : forall (A B : Type) (f : A -> B) n x y l,
  (n < length l) -> nth_default y (map f l) n = f (nth_default x l n).
Proof.
  intros A B f n x y l H.
  unfold nth_default.
  erewrite map_nth_error.
  reflexivity.
  nth_tac'.
  let H0 := match goal with H0 : _ = None |- _ => H0 end in
  pose proof (nth_error_error_length A n l H0).
  omega.
Qed.

Hint Rewrite @map_nth_default using omega : push_nth_default.

Ltac nth_tac :=
  repeat progress (try nth_tac'; try (match goal with
    | [ H: nth_error (map _ _) _ = Some _ |- _ ] => destruct (nth_error_map _ _ _ _ _ _ H); clear H
    | [ H: nth_error (seq _ _) _ = Some _ |- _ ] => rewrite nth_error_seq in H
    | [H: nth_error _ _ = None |- _ ] => specialize (nth_error_error_length _ _ _ H); intro; clear H
  end)).

Lemma app_cons_app_app : forall T xs (y:T) ys, xs ++ y :: ys = (xs ++ (y::nil)) ++ ys.
Proof. induction xs; boring. Qed.

Lemma unfold_set_nth {T} n x
  : forall xs,
    @set_nth T n x xs
    = match n with
      | O => match xs with
	     | nil => nil
	     | x'::xs' => x::xs'
	     end
      | S n' =>  match xs with
		 | nil => nil
		 | x'::xs' => x'::set_nth n' x xs'
		 end
      end.
Proof.
  induction n; destruct xs; reflexivity.
Qed.

Lemma simpl_set_nth_0 {T} x
  : forall xs,
    @set_nth T 0 x xs
    = match xs with
      | nil => nil
      | x'::xs' => x::xs'
      end.
Proof. intro; rewrite unfold_set_nth; reflexivity. Qed.

Lemma simpl_set_nth_S {T} x n
  : forall xs,
    @set_nth T (S n) x xs
    = match xs with
      | nil => nil
      | x'::xs' => x'::set_nth n x xs'
      end.
Proof. intro; rewrite unfold_set_nth; reflexivity. Qed.

Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_set_nth.

Lemma update_nth_ext {T} f g n
  : forall xs, (forall x, nth_error xs n = Some x -> f x = g x)
               -> @update_nth T n f xs = @update_nth T n g xs.
Proof.
  induction n as [|n IHn]; destruct xs; simpl; intros H;
    try rewrite IHn; try rewrite H;
      try congruence; trivial.
Qed.

Global Instance update_nth_Proper {T}
  : Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq) (@update_nth T).
Proof. repeat intro; subst; apply update_nth_ext; trivial. Qed.

Lemma update_nth_id_eq_specific {T} f n
  : forall (xs : list T) (H : forall x, nth_error xs n = Some x -> f x = x),
    update_nth n f xs = xs.
Proof.
  induction n as [|n IHn]; destruct xs; simpl; intros H;
    try rewrite IHn; try rewrite H; unfold value in *;
      try congruence; assumption.
Qed.

Hint Rewrite @update_nth_id_eq_specific using congruence : simpl_update_nth.

Lemma update_nth_id_eq : forall {T} f (H : forall x, f x = x) n (xs : list T),
    update_nth n f xs = xs.
Proof. intros; apply update_nth_id_eq_specific; trivial. Qed.

Hint Rewrite @update_nth_id_eq using congruence : simpl_update_nth.

Lemma update_nth_id : forall {T} n (xs : list T),
    update_nth n (fun x => x) xs = xs.
Proof. intros; apply update_nth_id_eq; trivial. Qed.

Hint Rewrite @update_nth_id : simpl_update_nth.

Lemma nth_update_nth : forall m {T} (xs:list T) (n:nat) (f:T -> T),
  nth_error (update_nth m f xs) n =
  if eq_nat_dec n m
  then option_map f (nth_error xs n)
  else nth_error xs n.
Proof.
  induction m as [|? IHm].
  { destruct n, xs; auto. }
  { destruct xs, n; intros; simpl; auto;
      [ | rewrite IHm ]; clear IHm;
        edestruct eq_nat_dec; reflexivity. }
Qed.

Hint Rewrite @nth_update_nth : push_nth_error.
Hint Rewrite <- @nth_update_nth : pull_nth_error.

Lemma length_update_nth : forall {T} i f (xs:list T), length (update_nth i f xs) = length xs.
Proof.
  induction i, xs; boring.
Qed.

Hint Rewrite @length_update_nth : distr_length.

Lemma nth_set_nth : forall m {T} (xs:list T) (n:nat) x,
  nth_error (set_nth m x xs) n =
  if eq_nat_dec n m
  then (if lt_dec n (length xs) then Some x else None)
  else nth_error xs n.
Proof.
  intros m T xs n x; unfold set_nth; rewrite nth_update_nth.
  destruct (nth_error xs n) eqn:?, (lt_dec n (length xs)) as [p|p];
    rewrite <- nth_error_Some in p;
    solve [ reflexivity
          | exfalso; apply p; congruence ].
Qed.

Hint Rewrite @nth_set_nth : push_nth_error.

Lemma length_set_nth : forall {T} i x (xs:list T), length (set_nth i x xs) = length xs.
Proof. intros; apply length_update_nth. Qed.

Hint Rewrite @length_set_nth : distr_length.

Lemma nth_error_length_exists_value : forall {A} (i : nat) (xs : list A),
  (i < length xs)%nat -> exists x, nth_error xs i = Some x.
Proof.
  induction i, xs; boring; try omega.
Qed.

Lemma nth_error_length_not_error : forall {A} (i : nat) (xs : list A),
  nth_error xs i = None -> (i < length xs)%nat -> False.
Proof.
  intros A i xs H H0.
  destruct (nth_error_length_exists_value i xs); intuition; congruence.
Qed.

Lemma nth_error_value_eq_nth_default : forall {T} i (x : T) xs,
  nth_error xs i = Some x -> forall d, nth_default d xs i = x.
Proof.
  unfold nth_default; boring.
Qed.

Hint Rewrite @nth_error_value_eq_nth_default using eassumption : simpl_nth_default.

Lemma skipn0 : forall {T} (xs:list T), skipn 0 xs = xs.
Proof. auto. Qed.

Lemma destruct_repeat : forall {A} xs y, (forall x : A, In x xs -> x = y) ->
  xs = nil \/ exists xs', xs = y :: xs' /\ (forall x : A, In x xs' -> x = y).
Proof.
  destruct xs as [|? xs]; intros; try tauto.
  right.
  exists xs; split.
  + f_equal; auto using in_eq.
  + intros; auto using in_cons.
Qed.

Lemma splice_nth_equiv_update_nth : forall {T} n f d (xs:list T),
  splice_nth n (f (nth_default d xs n)) xs =
  if lt_dec n (length xs)
  then update_nth n f xs
  else xs ++ (f d)::nil.
Proof.
  induction n, xs; boring_list; break_match; auto; omega.
Qed.

Lemma splice_nth_equiv_update_nth_update : forall {T} n f d (xs:list T),
  n < length xs ->
  splice_nth n (f (nth_default d xs n)) xs = update_nth n f xs.
Proof.
  intros.
  rewrite splice_nth_equiv_update_nth; break_match; auto; omega.
Qed.

Lemma splice_nth_equiv_update_nth_snoc : forall {T} n f d (xs:list T),
  n >= length xs ->
  splice_nth n (f (nth_default d xs n)) xs = xs ++ (f d)::nil.
Proof.
  intros.
  rewrite splice_nth_equiv_update_nth; break_match; auto; omega.
Qed.

Definition IMPOSSIBLE {T} : list T. exact nil. Qed.

Ltac remove_nth_error :=
  repeat match goal with
         | _ => exfalso; solve [ eauto using @nth_error_length_not_error ]
         | [ |- context[match nth_error ?ls ?n with _ => _ end] ]
           => destruct (nth_error ls n) eqn:?
         end.

Lemma update_nth_equiv_splice_nth: forall {T} n f (xs:list T),
  update_nth n f xs =
  if lt_dec n (length xs)
  then match nth_error xs n with
       | Some v => splice_nth n (f v) xs
       | None => IMPOSSIBLE
       end
  else xs.
Proof.
  induction n as [|? IHn]; destruct xs; intros;
    autorewrite with simpl_update_nth simpl_nth_default in *; simpl in *;
      try (erewrite IHn; clear IHn); auto.
  repeat break_match; remove_nth_error; try reflexivity; try omega.
Qed.

Lemma splice_nth_equiv_set_nth : forall {T} n x (xs:list T),
  splice_nth n x xs =
  if lt_dec n (length xs)
  then set_nth n x xs
  else xs ++ x::nil.
Proof. intros T n x xs; rewrite splice_nth_equiv_update_nth with (f := fun _ => x); auto. Qed.

Lemma splice_nth_equiv_set_nth_set : forall {T} n x (xs:list T),
  n < length xs ->
  splice_nth n x xs = set_nth n x xs.
Proof. intros T n x xs H; rewrite splice_nth_equiv_update_nth_update with (f := fun _ => x); auto. Qed.

Lemma splice_nth_equiv_set_nth_snoc : forall {T} n x (xs:list T),
  n >= length xs ->
  splice_nth n x xs = xs ++ x::nil.
Proof. intros T n x xs H; rewrite splice_nth_equiv_update_nth_snoc with (f := fun _ => x); auto. Qed.

Lemma set_nth_equiv_splice_nth: forall {T} n x (xs:list T),
  set_nth n x xs =
  if lt_dec n (length xs)
  then splice_nth n x xs
  else xs.
Proof.
  intros T n x xs; unfold set_nth; rewrite update_nth_equiv_splice_nth with (f := fun _ => x); auto.
  repeat break_match; remove_nth_error; trivial.
Qed.

Lemma combine_update_nth : forall {A B} n f g (xs:list A) (ys:list B),
  combine (update_nth n f xs) (update_nth n g ys) =
  update_nth n (fun xy => (f (fst xy), g (snd xy))) (combine xs ys).
Proof.
  induction n as [|? IHn]; destruct xs, ys; simpl; try rewrite IHn; reflexivity.
Qed.

(* grumble, grumble, [rewrite] is bad at inferring the identity function, and constant functions *)
Ltac rewrite_rev_combine_update_nth :=
  let lem := match goal with
             | [ |- context[update_nth ?n (fun xy => (@?f xy, @?g xy)) (combine ?xs ?ys)] ]
               => let f := match (eval cbv [fst] in (fun y x => f (x, y))) with
                           | fun _ => ?f => f
                           end in
                  let g := match (eval cbv [snd] in (fun x y => g (x, y))) with
                           | fun _ => ?g => g
                           end in
                  constr:(@combine_update_nth _ _ n f g xs ys)
             end in
  rewrite <- lem.

Lemma combine_update_nth_l : forall {A B} n (f : A -> A) xs (ys:list B),
  combine (update_nth n f xs) ys =
  update_nth n (fun xy => (f (fst xy), snd xy)) (combine xs ys).
Proof.
  intros ??? f xs ys.
  etransitivity; [ | apply combine_update_nth with (g := fun x => x) ].
  rewrite update_nth_id; reflexivity.
Qed.

Lemma combine_update_nth_r : forall {A B} n (g : B -> B) (xs:list A) (ys:list B),
  combine xs (update_nth n g ys) =
  update_nth n (fun xy => (fst xy, g (snd xy))) (combine xs ys).
Proof.
  intros ??? g xs ys.
  etransitivity; [ | apply combine_update_nth with (f := fun x => x) ].
  rewrite update_nth_id; reflexivity.
Qed.

Lemma combine_set_nth : forall {A B} n (x:A) xs (ys:list B),
  combine (set_nth n x xs) ys =
    match nth_error ys n with
    | None => combine xs ys
    | Some y => set_nth n (x,y) (combine xs ys)
    end.
Proof.
  intros A B n x xs ys; unfold set_nth; rewrite combine_update_nth_l.
  nth_tac;
    [ repeat rewrite_rev_combine_update_nth; apply f_equal2
    | assert (nth_error (combine xs ys) n = None)
      by (apply nth_error_None; rewrite combine_length; omega * ) ];
    autorewrite with simpl_update_nth; reflexivity.
Qed.

Lemma nth_error_value_In : forall {T} n xs (x:T),
  nth_error xs n = Some x -> In x xs.
Proof.
  induction n; destruct xs; nth_tac.
Qed.

Lemma In_nth_error_value : forall {T} xs (x:T),
  In x xs -> exists n, nth_error xs n = Some x.
Proof.
  induction xs as [|?? IHxs]; nth_tac; destruct_head or; subst.
  - exists 0; reflexivity.
  - edestruct IHxs as [x0]; eauto. exists (S x0). eauto.
Qed.

Lemma nth_value_index : forall {T} i xs (x:T),
  nth_error xs i = Some x -> In i (seq 0 (length xs)).
Proof.
  induction i as [|? IHi]; destruct xs; nth_tac; right.
  rewrite <- seq_shift; apply in_map; eapply IHi; eauto.
Qed.

Lemma nth_error_app : forall {T} n (xs ys:list T), nth_error (xs ++ ys) n =
  if lt_dec n (length xs)
  then nth_error xs n
  else nth_error ys (n - length xs).
Proof.
  induction n as [|n IHn]; destruct xs as [|? xs]; nth_tac;
    rewrite IHn; destruct (lt_dec n (length xs)); trivial; omega.
Qed.

Lemma nth_default_app : forall {T} n x (xs ys:list T), nth_default x (xs ++ ys) n =
  if lt_dec n (length xs)
  then nth_default x xs n
  else nth_default x ys (n - length xs).
Proof.
  intros T n x xs ys.
  unfold nth_default.
  rewrite nth_error_app.
  destruct (lt_dec n (length xs)); auto.
Qed.

Hint Rewrite @nth_default_app : push_nth_default.

Lemma combine_truncate_r : forall {A B} (xs : list A) (ys : list B),
  combine xs ys = combine xs (firstn (length xs) ys).
Proof.
  induction xs; destruct ys; boring.
Qed.

Lemma combine_truncate_l : forall {A B} (xs : list A) (ys : list B),
  combine xs ys = combine (firstn (length ys) xs) ys.
Proof.
  induction xs; destruct ys; boring.
Qed.

Lemma combine_app_samelength : forall {A B} (xs xs':list A) (ys ys':list B),
  length xs = length ys ->
  combine (xs ++ xs') (ys ++ ys') = combine xs ys ++ combine xs' ys'.
Proof.
  induction xs, xs', ys, ys'; boring; omega.
Qed.

Lemma map_fst_combine {A B} (xs:list A) (ys:list B) : List.map fst (List.combine xs ys) = List.firstn (length ys) xs.
Proof.
  revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
Qed.

Lemma map_snd_combine {A B} (xs:list A) (ys:list B) : List.map snd (List.combine xs ys) = List.firstn (length xs) ys.
Proof.
  revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
Qed.
Hint Rewrite @map_fst_combine @map_snd_combine : push_map.

Lemma skipn_nil : forall {A} n, skipn n nil = @nil A.
Proof. destruct n; auto. Qed.

Hint Rewrite @skipn_nil : simpl_skipn.
Hint Rewrite @skipn_nil : push_skipn.

Lemma skipn_0 : forall {A} xs, @skipn A 0 xs = xs.
Proof. reflexivity. Qed.

Hint Rewrite @skipn_0 : simpl_skipn.
Hint Rewrite @skipn_0 : push_skipn.

Lemma skipn_cons_S : forall {A} n x xs, @skipn A (S n) (x::xs) = @skipn A n xs.
Proof. reflexivity. Qed.

Hint Rewrite @skipn_cons_S : simpl_skipn.
Hint Rewrite @skipn_cons_S : push_skipn.

Lemma skipn_app : forall {A} n (xs ys : list A),
  skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys.
Proof.
  induction n, xs, ys; boring.
Qed.

Hint Rewrite @skipn_app : push_skipn.

Lemma skipn_skipn {A} n1 n2 (ls : list A)
  : skipn n2 (skipn n1 ls) = skipn (n1 + n2) ls.
Proof.
  revert n2 ls; induction n1, ls;
    simpl; autorewrite with simpl_skipn;
      boring.
Qed.

Hint Rewrite @skipn_skipn : simpl_skipn.
Hint Rewrite <- @skipn_skipn : push_skipn.
Hint Rewrite @skipn_skipn : pull_skipn.

Lemma skipn_firstn {A} (ls : list A) n m
  : skipn n (firstn m ls) = firstn (m - n) (skipn n ls).
Proof.
  revert n m; induction ls, m, n; simpl; autorewrite with simpl_skipn simpl_firstn; boring_list.
Qed.
Lemma firstn_skipn_add {A} (ls : list A) n m
  : firstn n (skipn m ls) = skipn m (firstn (m + n) ls).
Proof.
  revert n m; induction ls, m; simpl; autorewrite with simpl_skipn simpl_firstn; boring_list.
Qed.
Lemma firstn_skipn_add' {A} (ls : list A) n m
  : firstn n (skipn m ls) = skipn m (firstn (n + m) ls).
Proof. rewrite firstn_skipn_add; do 2 f_equal; auto with arith. Qed.
Hint Rewrite <- @firstn_skipn_add @firstn_skipn_add' : simpl_firstn.
Hint Rewrite <- @firstn_skipn_add @firstn_skipn_add' : simpl_skipn.

Lemma firstn_app_inleft : forall {A} n (xs ys : list A), (n <= length xs)%nat ->
  firstn n (xs ++ ys) = firstn n xs.
Proof.
  induction n, xs, ys; boring; try omega.
Qed.

Hint Rewrite @firstn_app_inleft using solve [ distr_length ] : simpl_firstn.
Hint Rewrite @firstn_app_inleft using solve [ distr_length ] : push_firstn.

Lemma skipn_app_inleft : forall {A} n (xs ys : list A), (n <= length xs)%nat ->
  skipn n (xs ++ ys) = skipn n xs ++ ys.
Proof.
  induction n, xs, ys; boring; try omega.
Qed.

Hint Rewrite @skipn_app_inleft using solve [ distr_length ] : push_skipn.

Lemma firstn_map : forall {A B} (f : A -> B) n (xs : list A), firstn n (map f xs) = map f (firstn n xs).
Proof. induction n, xs; boring. Qed.

Hint Rewrite @firstn_map : push_firstn.
Hint Rewrite <- @firstn_map : pull_firstn.

Lemma skipn_map : forall {A B} (f : A -> B) n (xs : list A), skipn n (map f xs) = map f (skipn n xs).
Proof. induction n, xs; boring. Qed.

Hint Rewrite @skipn_map : push_skipn.
Hint Rewrite <- @skipn_map : pull_skipn.

Lemma firstn_all : forall {A} n (xs:list A), n = length xs -> firstn n xs = xs.
Proof.
  induction n, xs; boring; omega.
Qed.

Hint Rewrite @firstn_all using solve [ distr_length ] : simpl_firstn.
Hint Rewrite @firstn_all using solve [ distr_length ] : push_firstn.

Lemma skipn_all : forall {T} n (xs:list T),
  (n >= length xs)%nat ->
  skipn n xs = nil.
Proof.
  induction n, xs; boring; omega.
Qed.

Hint Rewrite @skipn_all using solve [ distr_length ] : simpl_skipn.
Hint Rewrite @skipn_all using solve [ distr_length ] : push_skipn.

Lemma firstn_app_sharp : forall {A} n (l l': list A),
  length l = n ->
  firstn n (l ++ l') = l.
Proof.
  intros.
  rewrite firstn_app_inleft; auto using firstn_all; omega.
Qed.

Hint Rewrite @firstn_app_sharp using solve [ distr_length ] : simpl_firstn.
Hint Rewrite @firstn_app_sharp using solve [ distr_length ] : push_firstn.

Lemma skipn_app_sharp : forall {A} n (l l': list A),
  length l = n ->
  skipn n (l ++ l') = l'.
Proof.
  intros.
  rewrite skipn_app_inleft; try rewrite skipn_all; auto; omega.
Qed.

Hint Rewrite @skipn_app_sharp using solve [ distr_length ] : simpl_skipn.
Hint Rewrite @skipn_app_sharp using solve [ distr_length ] : push_skipn.

Lemma skipn_length : forall {A} n (xs : list A),
  length (skipn n xs) = (length xs - n)%nat.
Proof.
  induction n, xs; boring.
Qed.

Hint Rewrite @skipn_length : distr_length.

Lemma length_cons : forall {T} (x:T) xs, length (x::xs) = S (length xs).
  reflexivity.
Qed.

Hint Rewrite @length_cons : distr_length.

Lemma length_cons_full {T} n (x:list T) (t:T) (H: length (t :: x) = S n)
  : length x = n.
Proof. distr_length. Qed.

Lemma cons_length : forall A (xs : list A) a, length (a :: xs) = S (length xs).
Proof.
  auto.
Qed.

Lemma length0_nil : forall {A} (xs : list A), length xs = 0%nat -> xs = nil.
Proof.
  induction xs; boring; discriminate.
Qed.

Lemma length_snoc : forall {T} xs (x:T),
  length xs = pred (length (xs++x::nil)).
Proof.
  boring; simpl_list; boring.
Qed.

Lemma combine_cons : forall {A B} a b (xs:list A) (ys:list B),
  combine (a :: xs) (b :: ys) = (a,b) :: combine xs ys.
Proof. reflexivity. Qed.

Lemma firstn_combine : forall {A B} n (xs:list A) (ys:list B),
  firstn n (combine xs ys) = combine (firstn n xs) (firstn n ys).
Proof.
  induction n, xs, ys; boring.
Qed.

Hint Rewrite @firstn_combine : push_firstn.
Hint Rewrite <- @firstn_combine : pull_firstn.

Lemma combine_nil_r : forall {A B} (xs:list A),
  combine xs (@nil B) = nil.
Proof.
  induction xs; boring.
Qed.

Lemma skipn_combine : forall {A B} n (xs:list A) (ys:list B),
  skipn n (combine xs ys) = combine (skipn n xs) (skipn n ys).
Proof.
  induction n, xs, ys; boring.
  rewrite combine_nil_r; reflexivity.
Qed.

Hint Rewrite @skipn_combine : push_skipn.
Hint Rewrite <- @skipn_combine : pull_skipn.

Lemma break_list_last: forall {T} (xs:list T),
  xs = nil \/ exists xs' y, xs = xs' ++ y :: nil.
Proof.
  destruct xs using rev_ind; auto.
  right; do 2 eexists; auto.
Qed.

Lemma break_list_first: forall {T} (xs:list T),
  xs = nil \/ exists x xs', xs = x :: xs'.
Proof.
  destruct xs; auto.
  right; do 2 eexists; auto.
Qed.

Lemma list012 : forall {T} (xs:list T),
  xs = nil
  \/ (exists x, xs = x::nil)
  \/ (exists x xs' y, xs = x::xs'++y::nil).
Proof.
  destruct xs as [|? xs]; auto.
  right.
  destruct xs using rev_ind. {
    left; eexists; auto.
  } {
    right; repeat eexists; auto.
  }
Qed.

Lemma nil_length0 : forall {T}, length (@nil T) = 0%nat.
Proof.
  auto.
Qed.

Hint Rewrite @nil_length0 : distr_length.

Lemma nth_error_Some_nth_default : forall {T} i x (l : list T), (i < length l)%nat ->
  nth_error l i = Some (nth_default x l i).
Proof.
  intros ? ? ? ? i_lt_length.
  destruct (nth_error_length_exists_value _ _ i_lt_length) as [k nth_err_k].
  unfold nth_default.
  rewrite nth_err_k.
  reflexivity.
Qed.

Lemma update_nth_cons : forall {T} f (u0 : T) us, update_nth 0 f (u0 :: us) = (f u0) :: us.
Proof. reflexivity. Qed.

Hint Rewrite @update_nth_cons : simpl_update_nth.

Lemma set_nth_cons : forall {T} (x u0 : T) us, set_nth 0 x (u0 :: us) = x :: us.
Proof. intros; apply update_nth_cons. Qed.

Hint Rewrite @set_nth_cons : simpl_set_nth.

Lemma cons_update_nth : forall {T} n f (y : T) us,
  y :: update_nth n f us = update_nth (S n) f (y :: us).
Proof.
  induction n; boring.
Qed.

Hint Rewrite <- @cons_update_nth : simpl_update_nth.

Lemma update_nth_nil : forall {T} n f, update_nth n f (@nil T) = @nil T.
Proof.
  induction n; boring.
Qed.

Hint Rewrite @update_nth_nil : simpl_update_nth.

Lemma cons_set_nth : forall {T} n (x y : T) us,
  y :: set_nth n x us = set_nth (S n) x (y :: us).
Proof. intros; apply cons_update_nth. Qed.

Hint Rewrite <- @cons_set_nth : simpl_set_nth.

Lemma set_nth_nil : forall {T} n (x : T), set_nth n x nil = nil.
Proof. intros; apply update_nth_nil. Qed.

Hint Rewrite @set_nth_nil : simpl_set_nth.

Lemma skipn_nth_default : forall {T} n us (d : T), (n < length us)%nat ->
 skipn n us = nth_default d us n :: skipn (S n) us.
Proof.
  induction n as [|n IHn]; destruct us as [|? us]; intros d H; nth_tac.
  rewrite (IHn us d) at 1 by omega.
  nth_tac.
Qed.

Lemma nth_default_out_of_bounds : forall {T} n us (d : T), (n >= length us)%nat ->
  nth_default d us n = d.
Proof.
  induction n as [|n IHn]; unfold nth_default; nth_tac;
    let us' := match goal with us : list _ |- _ => us end in
    destruct us' as [|? us]; nth_tac.
  assert (n >= length us)%nat by omega.
  pose proof (nth_error_length_error _ n us).
  specialize_by_assumption.
  rewrite_hyp * in *.
  congruence.
Qed.

Hint Rewrite @nth_default_out_of_bounds using omega : simpl_nth_default.

Ltac nth_error_inbounds :=
  match goal with
  | [ |- context[match nth_error ?xs ?i with Some _ => _ | None => _ end ] ] =>
    case_eq (nth_error xs i);
    match goal with
      | [ |- forall _, nth_error xs i = Some _ -> _ ] =>
          let x := fresh "x" in
          let H := fresh "H" in
          intros x H;
          repeat progress erewrite H;
          repeat progress erewrite (nth_error_value_eq_nth_default i xs x); auto
      | [ |- nth_error xs i = None -> _ ] =>
          let H := fresh "H" in
          intros H;
          destruct (nth_error_length_not_error _ _ H);
          try solve [distr_length]
    end;
    idtac
  end.
Ltac set_nth_inbounds :=
  match goal with
  | [ |- context[set_nth ?i ?x ?xs] ] =>
    rewrite (set_nth_equiv_splice_nth i x xs);
    destruct (lt_dec i (length xs));
    match goal with
    | [ H : ~ (i < (length xs))%nat |- _ ] => destruct H
    | [ H :   (i < (length xs))%nat |- _ ] => try solve [distr_length]
    end
  end.
Ltac update_nth_inbounds :=
  match goal with
  | [ |- context[update_nth ?i ?f ?xs] ] =>
    rewrite (update_nth_equiv_splice_nth i f xs);
    destruct (lt_dec i (length xs));
    match goal with
    | [ H : ~ (i < (length xs))%nat |- _ ] => destruct H
    | [ H :   (i < (length xs))%nat |- _ ] => remove_nth_error; try solve [distr_length]
    end
  end.

Ltac nth_inbounds := nth_error_inbounds || set_nth_inbounds || update_nth_inbounds.

Definition nth_dep {A} (ls : list A) (n : nat) (pf : n < length ls) : A.
Proof.
  refine (match nth_error ls n as v return nth_error ls n = v -> A with
          | Some v => fun _ => v
          | None => fun bad => match _ : False with end
          end eq_refl).
  apply (proj1 (@nth_error_None _ _ _)) in bad; instantiate; generalize dependent (length ls); clear.
  abstract (intros; omega).
Defined.

Lemma nth_error_nth_dep {A} ls n pf : nth_error ls n = Some (@nth_dep A ls n pf).
Proof.
  unfold nth_dep.
  generalize dependent (@nth_error_None A ls n).
  edestruct nth_error; boring.
Qed.

Lemma nth_default_nth_dep {A} d ls n pf : nth_default d ls n = @nth_dep A ls n pf.
Proof.
  unfold nth_dep.
  generalize dependent (@nth_error_None A ls n).
  destruct (nth_error ls n) eqn:?; boring.
  erewrite nth_error_value_eq_nth_default by eassumption; reflexivity.
Qed.

Lemma nth_default_in_bounds : forall {T} (d' d : T) n us, (n < length us)%nat ->
  nth_default d us n = nth_default d' us n.
Proof.
  intros; erewrite !nth_default_nth_dep; reflexivity.
  Grab Existential Variables.
  assumption.
Qed.

Hint Resolve @nth_default_in_bounds : simpl_nth_default.

Lemma cons_eq_head : forall {T} (x y:T) xs ys, x::xs = y::ys -> x=y.
Proof.
  intros; congruence.
Qed.
Lemma cons_eq_tail : forall {T} (x y:T) xs ys, x::xs = y::ys -> xs=ys.
Proof.
  intros; congruence.
Qed.

Lemma map_nth_default_always {A B} (f : A -> B) (n : nat) (x : A) (l : list A)
  : nth_default (f x) (map f l) n = f (nth_default x l n).
Proof.
  revert n; induction l; simpl; intro n; destruct n; [ try reflexivity.. ].
  nth_tac.
Qed.

Hint Rewrite @map_nth_default_always : push_nth_default.

Lemma map_S_seq {A} (f:nat->A) len : forall start,
  List.map (fun i => f (S i)) (seq start len) = List.map f (seq (S start) len).
Proof. induction len as [|len IHlen]; intros; simpl; rewrite ?IHlen; reflexivity. Qed.

Lemma fold_right_and_True_forall_In_iff : forall {T} (l : list T) (P : T -> Prop),
  (forall x, In x l -> P x) <-> fold_right and True (map P l).
Proof.
  induction l as [|?? IHl]; intros; simpl; try tauto.
  rewrite <- IHl.
  intuition (subst; auto).
Qed.

Lemma fold_right_invariant : forall {A B} P (f: A -> B -> B) l x,
  P x -> (forall y, In y l -> forall z, P z -> P (f y z)) ->
  P (fold_right f x l).
Proof.
  induction l as [|a l IHl]; intros ? ? step; auto.
  simpl.
  apply step; try apply in_eq.
  apply IHl; auto.
  intros y in_y_l.
  apply (in_cons a) in in_y_l.
  auto.
Qed.

Lemma In_firstn : forall {T} n l (x : T), In x (firstn n l) -> In x l.
Proof.
  induction n; destruct l; boring.
Qed.

Lemma In_skipn : forall {T} n l (x : T), In x (skipn n l) -> In x l.
Proof.
  induction n; destruct l; boring.
Qed.

Lemma In_firstn_skipn_split {T} n (x : T)
  : forall l, In x l <-> In x (firstn n l) \/ In x (skipn n l).
Proof.
  intro l; split; revert l; induction n; destruct l; boring.
  match goal with
  | [ IH : forall l, In ?x l -> _ \/ _, H' : In ?x ?ls |- _ ]
    => destruct (IH _ H')
  end; auto.
Qed.

Lemma firstn_firstn_min : forall {A} m n (l : list A),
    firstn n (firstn m l) = firstn (min n m) l.
Proof.
  induction m as [|? IHm]; destruct n; intros l; try omega; auto.
  destruct l; auto.
  simpl.
  f_equal.
  apply IHm; omega.
Qed.

Lemma firstn_firstn : forall {A} m n (l : list A), (n <= m)%nat ->
  firstn n (firstn m l) = firstn n l.
Proof.
  intros A m n l H; rewrite firstn_firstn_min.
  apply Min.min_case_strong; intro; [ reflexivity | ].
  assert (n = m) by omega; subst; reflexivity.
Qed.

Hint Rewrite @firstn_firstn using omega : push_firstn.

Lemma firstn_succ : forall {A} (d : A) n l, (n < length l)%nat ->
  firstn (S n) l = (firstn n l) ++ nth_default d l n :: nil.
Proof.
  intros A d; induction n as [|? IHn]; destruct l; rewrite ?(@nil_length0 A); intros; try omega.
  + rewrite nth_default_cons; auto.
  + simpl.
    rewrite nth_default_cons_S.
    rewrite <-IHn by (rewrite cons_length in *; omega).
    reflexivity.
Qed.

Lemma firstn_seq k a b
  : firstn k (seq a b) = seq a (min k b).
Proof.
  revert k a; induction b as [|? IHb], k; simpl; try reflexivity.
  intros; rewrite IHb; reflexivity.
Qed.

Lemma skipn_seq k a b
  : skipn k (seq a b) = seq (k + a) (b - k).
Proof.
  revert k a; induction b as [|? IHb], k; simpl; try reflexivity.
  intros; rewrite IHb; simpl; f_equal; omega.
Qed.

Lemma update_nth_out_of_bounds : forall {A} n f xs, n >= length xs -> @update_nth A n f xs = xs.
Proof.
  induction n as [|n IHn]; destruct xs; simpl; try congruence; try omega; intros.
  rewrite IHn by omega; reflexivity.
Qed.

Hint Rewrite @update_nth_out_of_bounds using omega : simpl_update_nth.


Lemma update_nth_nth_default_full : forall {A} (d:A) n f l i,
  nth_default d (update_nth n f l) i =
  if lt_dec i (length l) then
    if (eq_nat_dec i n) then f (nth_default d l i)
    else nth_default d l i
  else d.
Proof.
  induction n as [|n IHn]; (destruct l; simpl in *; [ intros i **; destruct i; simpl; try reflexivity; omega | ]);
    intros i **; repeat break_match; subst; try destruct i;
      repeat first [ progress break_match
                   | progress subst
                   | progress boring
                   | progress autorewrite with simpl_nth_default
                   | omega ].
Qed.

Hint Rewrite @update_nth_nth_default_full : push_nth_default.

Lemma update_nth_nth_default : forall {A} (d:A) n f l i, (0 <= i < length l)%nat ->
  nth_default d (update_nth n f l) i =
  if (eq_nat_dec i n) then f (nth_default d l i) else nth_default d l i.
Proof. intros; rewrite update_nth_nth_default_full; repeat break_match; boring. Qed.

Hint Rewrite @update_nth_nth_default using (omega || distr_length; omega) : push_nth_default.

Lemma set_nth_nth_default_full : forall {A} (d:A) n v l i,
  nth_default d (set_nth n v l) i =
  if lt_dec i (length l) then
    if (eq_nat_dec i n) then v
    else nth_default d l i
  else d.
Proof. intros; apply update_nth_nth_default_full; assumption. Qed.

Hint Rewrite @set_nth_nth_default_full : push_nth_default.

Lemma set_nth_nth_default : forall {A} (d:A) n x l i, (0 <= i < length l)%nat ->
  nth_default d (set_nth n x l) i =
  if (eq_nat_dec i n) then x else nth_default d l i.
Proof. intros; apply update_nth_nth_default; assumption. Qed.

Hint Rewrite @set_nth_nth_default using (omega || distr_length; omega) : push_nth_default.

Lemma nth_default_preserves_properties : forall {A} (P : A -> Prop) l n d,
  (forall x, In x l -> P x) -> P d -> P (nth_default d l n).
Proof.
  intros A P l n d H H0; rewrite nth_default_eq.
  destruct (nth_in_or_default n l d); auto.
  congruence.
Qed.

Lemma nth_default_preserves_properties_length_dep :
  forall {A} (P : A -> Prop) l n d,
  (forall x, In x l -> n < (length l) -> P x) -> ((~ n < length l) -> P d) -> P (nth_default d l n).
Proof.
  intros A P l n d H H0.
  destruct (lt_dec n (length l)).
  + rewrite nth_default_eq; auto using nth_In.
  + rewrite nth_default_out_of_bounds by omega.
    auto.
Qed.

Lemma nth_error_first : forall {T} (a b : T) l,
  nth_error (a :: l) 0 = Some b -> a = b.
Proof.
  intros; simpl in *.
  unfold value in *.
  congruence.
Qed.

Lemma nth_error_exists_first : forall {T} l (x : T) (H : nth_error l 0 = Some x),
  exists l', l = x :: l'.
Proof.
  induction l; try discriminate; intros x H; eexists.
  apply nth_error_first in H.
  subst; eauto.
Qed.

Lemma list_elementwise_eq : forall {T} (l1 l2 : list T),
  (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  induction l1, l2; intros H; try reflexivity;
    pose proof (H 0%nat) as Hfirst; simpl in Hfirst; inversion Hfirst.
  f_equal.
  apply IHl1.
  intros i; specialize (H (S i)).
  boring.
Qed.

Lemma sum_firstn_all_succ : forall n l, (length l <= n)%nat ->
  sum_firstn l (S n) = sum_firstn l n.
Proof.
  unfold sum_firstn; intros.
  autorewrite with push_firstn; reflexivity.
Qed.

Hint Rewrite @sum_firstn_all_succ using omega : simpl_sum_firstn.

Lemma sum_firstn_all : forall n l, (length l <= n)%nat ->
  sum_firstn l n = sum_firstn l (length l).
Proof.
  unfold sum_firstn; intros.
  autorewrite with push_firstn; reflexivity.
Qed.

Hint Rewrite @sum_firstn_all using omega : simpl_sum_firstn.

Lemma sum_firstn_succ_default : forall l i,
  sum_firstn l (S i) = (nth_default 0 l i + sum_firstn l i)%Z.
Proof.
  unfold sum_firstn; induction l as [|a l IHl], i;
    intros; autorewrite with simpl_nth_default simpl_firstn simpl_fold_right in *;
      try reflexivity.
  rewrite IHl; omega.
Qed.

Hint Rewrite @sum_firstn_succ_default : simpl_sum_firstn.

Lemma sum_firstn_0 : forall xs,
  sum_firstn xs 0 = 0%Z.
Proof.
  destruct xs; reflexivity.
Qed.

Hint Rewrite @sum_firstn_0 : simpl_sum_firstn.

Lemma sum_firstn_succ : forall l i x,
  nth_error l i = Some x ->
  sum_firstn l (S i) = (x + sum_firstn l i)%Z.
Proof.
  intros; rewrite sum_firstn_succ_default.
  erewrite nth_error_value_eq_nth_default by eassumption; reflexivity.
Qed.

Hint Rewrite @sum_firstn_succ using congruence : simpl_sum_firstn.

Lemma sum_firstn_succ_cons : forall x xs i,
  sum_firstn (x :: xs) (S i) = (x + sum_firstn xs i)%Z.
Proof.
  unfold sum_firstn; simpl; reflexivity.
Qed.

Hint Rewrite @sum_firstn_succ_cons : simpl_sum_firstn.

Lemma sum_firstn_nil : forall i,
  sum_firstn nil i = 0%Z.
Proof. destruct i; reflexivity. Qed.

Hint Rewrite @sum_firstn_nil : simpl_sum_firstn.

Lemma sum_firstn_succ_default_rev : forall l i,
  sum_firstn l i = (sum_firstn l (S i) - nth_default 0 l i)%Z.
Proof.
  intros; rewrite sum_firstn_succ_default; omega.
Qed.

Lemma sum_firstn_succ_rev : forall l i x,
  nth_error l i = Some x ->
  sum_firstn l i = (sum_firstn l (S i) - x)%Z.
Proof.
  intros; erewrite sum_firstn_succ by eassumption; omega.
Qed.

Lemma sum_firstn_nonnegative : forall n l, (forall x, In x l -> 0 <= x)%Z
                                       -> (0 <= sum_firstn l n)%Z.
Proof.
  induction n as [|n IHn]; destruct l as [|? l]; autorewrite with simpl_sum_firstn; simpl; try omega.
  { specialize (IHn l).
    destruct n; simpl; autorewrite with simpl_sum_firstn simpl_nth_default in *;
      intuition auto with zarith. }
Qed.

Hint Resolve sum_firstn_nonnegative : znonzero.

Lemma sum_firstn_app : forall xs ys n,
  sum_firstn (xs ++ ys) n = (sum_firstn xs n + sum_firstn ys (n - length xs))%Z.
Proof.
  induction xs as [|a xs IHxs]; simpl.
  { intros ys n; autorewrite with simpl_sum_firstn; simpl.
    f_equal; omega. }
  { intros ys [|n]; autorewrite with simpl_sum_firstn; simpl; [ reflexivity | ].
    rewrite IHxs; omega. }
Qed.

Lemma sum_firstn_app_sum : forall xs ys n,
  sum_firstn (xs ++ ys) (length xs + n) = (sum_firstn xs (length xs) + sum_firstn ys n)%Z.
Proof.
  intros; rewrite sum_firstn_app; autorewrite with simpl_sum_firstn.
  do 2 f_equal; omega.
Qed.
Hint Rewrite @sum_firstn_app_sum : simpl_sum_firstn.

Lemma sum_cons xs x : sum (x :: xs) = (x + sum xs)%Z.
Proof. reflexivity. Qed.

Lemma sum_nil : sum nil = 0%Z.
Proof. reflexivity. Qed.

Lemma nth_error_skipn : forall {A} n (l : list A) m,
nth_error (skipn n l) m = nth_error l (n + m).
Proof.
induction n as [|n IHn]; destruct l; boring.
apply nth_error_nil_error.
Qed.
Hint Rewrite @nth_error_skipn : push_nth_error.

Lemma nth_default_skipn : forall {A} (l : list A) d n m, nth_default d (skipn n l) m = nth_default d l (n + m).
Proof.
cbv [nth_default]; intros.
rewrite nth_error_skipn.
reflexivity.
Qed.
Hint Rewrite @nth_default_skipn : push_nth_default.

Lemma sum_firstn_skipn : forall l n m, sum_firstn l (n + m) = (sum_firstn l n + sum_firstn (skipn n l) m)%Z.
Proof.
induction m; intros.
+ rewrite sum_firstn_0. autorewrite with natsimplify. omega.
+ rewrite <-plus_n_Sm, !sum_firstn_succ_default.
    rewrite nth_default_skipn.
    omega.
Qed.

Lemma nth_default_seq_inbounds d s n i (H:(i < n)%nat) :
  List.nth_default d (List.seq s n) i = (s+i)%nat.
Proof.
  progress cbv [List.nth_default].
  rewrite nth_error_seq.
  break_innermost_match; solve [ trivial | omega ].
Qed.
Hint Rewrite @nth_default_seq_inbounds using lia : push_nth_default.

Lemma sum_firstn_prefix_le' : forall l n m, (forall x, In x l -> (0 <= x)%Z) ->
                                            (sum_firstn l n <= sum_firstn l (n + m))%Z.
Proof.
intros l n m H.
rewrite sum_firstn_skipn.
pose proof (sum_firstn_nonnegative m (skipn n l)) as Hskipn_nonneg.
match type of Hskipn_nonneg with
  ?P -> _ => assert P as Q; [ | specialize (Hskipn_nonneg Q); omega ] end.
intros x HIn_skipn.
apply In_skipn in HIn_skipn.
auto.
Qed.

Lemma sum_firstn_prefix_le : forall l n m, (forall x, In x l -> (0 <= x)%Z) ->
                                            (n <= m)%nat ->
                                            (sum_firstn l n <= sum_firstn l m)%Z.
Proof.
intros l n m H H0.
replace m with (n + (m - n))%nat by omega.
auto using sum_firstn_prefix_le'.
Qed.

Lemma sum_firstn_pos_lt_succ : forall l n m, (forall x, In x l -> (0 <= x)%Z) ->
                                        (n < length l)%nat ->
                                        (sum_firstn l n < sum_firstn l (S m))%Z ->
                                        (n <= m)%nat.
Proof.
intros l n m H H0 H1.
destruct (le_dec n m); auto.
replace n with (m + (n - m))%nat in H1 by omega.
rewrite sum_firstn_skipn in H1.
rewrite sum_firstn_succ_default in *.
match goal with H : (?a + ?b < ?c + ?a)%Z |- _ => assert (H2 : (b < c)%Z) by omega end.
destruct (lt_dec m (length l)). {
    rewrite skipn_nth_default with (d := 0%Z) in H2 by assumption.
    replace (n - m)%nat with (S (n - S m))%nat in H2 by omega.
    rewrite sum_firstn_succ_cons in H2.
    pose proof (sum_firstn_nonnegative (n - S m) (skipn (S m) l)) as H3.
    match type of H3 with
      ?P -> _ => assert P as Q; [ | specialize (H3 Q); omega ] end.
    intros ? A.
    apply In_skipn in A.
    apply H in A.
    omega.
} {
    rewrite skipn_all, nth_default_out_of_bounds in H2 by omega.
    rewrite sum_firstn_nil in H2; omega.
}
Qed.

Definition NotSum {T} (xs : list T) (v : nat) := True.

Ltac NotSum :=
  lazymatch goal with
  | [ |- NotSum ?xs (length ?xs + _)%nat ] => fail
  | [ |- NotSum _ _ ] => exact I
  end.

Lemma sum_firstn_app_hint : forall xs ys n, NotSum xs n ->
  sum_firstn (xs ++ ys) n = (sum_firstn xs n + sum_firstn ys (n - length xs))%Z.
Proof. auto using sum_firstn_app. Qed.

Hint Rewrite sum_firstn_app_hint using solve [ NotSum ] : simpl_sum_firstn.


Lemma nth_default_map2 : forall {A B C} (f : A -> B -> C) ls1 ls2 i d d1 d2,
  nth_default d (map2 f ls1 ls2) i =
    if lt_dec i (min (length ls1) (length ls2))
    then f (nth_default d1 ls1 i) (nth_default d2 ls2 i)
    else d.
Proof.
  induction ls1 as [|a ls1 IHls1], ls2.
  + cbv [map2 length min].
    intros.
    break_match; try omega.
    apply nth_default_nil.
  + cbv [map2 length min].
    intros.
    break_match; try omega.
    apply nth_default_nil.
  + cbv [map2 length min].
    intros.
    break_match; try omega.
    apply nth_default_nil.
  + simpl.
    destruct i.
    - intros. rewrite !nth_default_cons.
      break_match; auto; omega.
    - intros d d1 d2. rewrite !nth_default_cons_S.
      rewrite IHls1 with (d1 := d1) (d2 := d2).
      repeat break_match; auto; omega.
Qed.

Lemma map2_cons : forall A B C (f : A -> B -> C) ls1 ls2 a b,
  map2 f (a :: ls1) (b :: ls2) = f a b :: map2 f ls1 ls2.
Proof.
  reflexivity.
Qed.

Lemma map2_nil_l : forall A B C (f : A -> B -> C) ls2,
  map2 f nil ls2 = nil.
Proof.
  reflexivity.
Qed.

Lemma map2_nil_r : forall A B C (f : A -> B -> C) ls1,
  map2 f ls1 nil = nil.
Proof.
  destruct ls1; reflexivity.
Qed.
Local Hint Resolve map2_nil_r map2_nil_l.

Ltac simpl_list_lengths := repeat match goal with
                                  | H : context[length (@nil ?A)] |- _ => rewrite (@nil_length0 A) in H
                                  | H : context[length (_ :: _)] |- _ => rewrite length_cons in H
                                  | |- context[length (@nil ?A)] => rewrite (@nil_length0 A)
                                  | |- context[length (_ :: _)] => rewrite length_cons
                                  end.

Section OpaqueMap2.
  Local Opaque map2.

  Lemma map2_length : forall A B C (f : A -> B -> C) ls1 ls2,
      length (map2 f ls1 ls2) = min (length ls1) (length ls2).
  Proof.
    induction ls1 as [|a ls1 IHls1], ls2; intros; try solve [cbv; auto].
    rewrite map2_cons, !length_cons, IHls1.
    auto.
  Qed.
  Hint Rewrite @map2_length : distr_length.


  Lemma map2_app : forall A B C (f : A -> B -> C) ls1 ls2 ls1' ls2',
      (length ls1 = length ls2) ->
      map2 f (ls1 ++ ls1') (ls2 ++ ls2') = map2 f ls1 ls2 ++ map2 f ls1' ls2'.
  Proof.
    induction ls1 as [|a ls1 IHls1], ls2; intros; rewrite ?map2_nil_r, ?app_nil_l; try congruence;
      simpl_list_lengths; try omega.
    rewrite <-!app_comm_cons, !map2_cons.
    rewrite IHls1; auto.
  Qed.
End OpaqueMap2.

Lemma firstn_update_nth {A}
  : forall f m n (xs : list A), firstn m (update_nth n f xs) = update_nth n f (firstn m xs).
Proof.
  induction m; destruct n, xs;
    autorewrite with simpl_firstn simpl_update_nth;
    congruence.
Qed.

Hint Rewrite @firstn_update_nth : push_firstn.
Hint Rewrite @firstn_update_nth : pull_update_nth.
Hint Rewrite <- @firstn_update_nth : pull_firstn.
Hint Rewrite <- @firstn_update_nth : push_update_nth.

Require Import Coq.Lists.SetoidList.
Global Instance Proper_nth_default : forall A eq,
  Proper (eq==>eqlistA eq==>Logic.eq==>eq) (nth_default (A:=A)).
Proof.
  intros A ee x y H; subst; induction 1.
  + repeat intro; rewrite !nth_default_nil; assumption.
  + intros x1 y0 H2; subst; destruct y0; rewrite ?nth_default_cons, ?nth_default_cons_S; auto.
Qed.

Lemma fold_right_andb_true_map_iff A (ls : list A) f
  : List.fold_right andb true (List.map f ls) = true <-> forall i, List.In i ls -> f i = true.
Proof.
  induction ls as [|a ls IHls]; simpl; [ | rewrite Bool.andb_true_iff, IHls ]; try tauto.
  intuition (congruence || eauto).
Qed.

Lemma fold_right_andb_true_iff_fold_right_and_True (ls : list bool)
  : List.fold_right andb true ls = true <-> List.fold_right and True (List.map (fun b => b = true) ls).
Proof.
  rewrite <- (map_id ls) at 1.
  rewrite fold_right_andb_true_map_iff, fold_right_and_True_forall_In_iff; reflexivity.
Qed.

Lemma Forall2_forall_iff : forall {A} R (xs ys : list A) d, length xs = length ys ->
  (Forall2 R xs ys <-> (forall i, (i < length xs)%nat -> R (nth_default d xs i) (nth_default d ys i))).
Proof.
  intros A R xs ys d H; split; [ intros H0 i H1 | intros H0 ].

  + revert xs ys H H0 H1.
    induction i as [|i IHi]; intros xs ys H H0 H1; destruct H0; distr_length; autorewrite with push_nth_default; auto.
    eapply IHi; auto. omega.
  + revert xs ys H H0; induction xs as [|a xs IHxs]; intros ys H H0; destruct ys; distr_length; econstructor.
    - specialize (H0 0%nat).
      autorewrite with push_nth_default in *; auto.
      apply H0; omega.
    - apply IHxs; try omega.
      intros i H1.
      specialize (H0 (S i)).
      autorewrite with push_nth_default in *; auto.
      apply H0; omega.
Qed.

Lemma nth_default_firstn : forall {A} (d : A) l i n,
  nth_default d (firstn n l) i = if le_dec n (length l)
                                 then if lt_dec i n then nth_default d l i else d
                                 else nth_default d l i.
Proof.
  intros A d l i; induction n as [|n IHn]; break_match; autorewrite with push_nth_default; auto; try omega.
  + rewrite (firstn_succ d) by omega.
    autorewrite with push_nth_default; repeat (break_match_hyps; break_match; distr_length);
      rewrite Min.min_l in * by omega; try omega.
    - apply IHn; omega.
    - replace i with n in * by omega.
      rewrite Nat.sub_diag.
      autorewrite with push_nth_default; auto.
  + rewrite nth_default_out_of_bounds; break_match_hyps; distr_length; auto; lia.
  + rewrite firstn_all2 by omega.
    auto.
Qed.
Hint Rewrite @nth_default_firstn : push_nth_default.

Lemma nth_error_repeat {T} x n i v : nth_error (@repeat T x n) i = Some v -> v = x.
Proof.
  revert n x v; induction i as [|i IHi]; destruct n; simpl in *; eauto; congruence.
Qed.

Hint Rewrite repeat_length : distr_length.

Lemma repeat_spec_iff : forall {A} (ls : list A) x n,
    (length ls = n /\ forall y, In y ls -> y = x) <-> ls = repeat x n.
Proof.
  intros A ls x n; split; [ revert A ls x n | intro; subst; eauto using repeat_length, repeat_spec ].
  induction ls as [|a ls IHls], n; simpl; intros; intuition try congruence.
  f_equal; auto.
Qed.

Lemma repeat_spec_eq : forall {A} (ls : list A) x n,
    length ls = n
    -> (forall y, In y ls -> y = x)
    -> ls = repeat x n.
Proof.
  intros; apply repeat_spec_iff; auto.
Qed.

Lemma tl_repeat {A} x n : tl (@repeat A x n) = repeat x (pred n).
Proof. destruct n; reflexivity. Qed.

Lemma firstn_repeat : forall {A} x n k, firstn k (@repeat A x n) = repeat x (min k n).
Proof. induction n, k; boring. Qed.

Hint Rewrite @firstn_repeat : push_firstn.

Lemma skipn_repeat : forall {A} x n k, skipn k (@repeat A x n) = repeat x (n - k).
Proof. induction n, k; boring. Qed.

Hint Rewrite @skipn_repeat : push_skipn.

Global Instance Proper_map {A B} {RA RB} {Equivalence_RB:Equivalence RB}
  : Proper ((RA==>RB) ==> eqlistA RA ==> eqlistA RB) (@List.map A B).
Proof.
  repeat intro.
  match goal with [H:eqlistA _ _ _ |- _ ] => induction H end; [reflexivity|].
  cbv [respectful] in *; econstructor; eauto.
Qed.

Lemma pointwise_map {A B} : Proper ((pointwise_relation _ eq) ==> eq ==> eq) (@List.map A B).
Proof.
  repeat intro; cbv [pointwise_relation] in *; subst.
  match goal with [H:list _ |- _ ] => induction H as [|? IH IHIH] end; [reflexivity|].
  simpl. rewrite IHIH. congruence.
Qed.

Lemma map_map2 {A B C D} (f:A -> B -> C) (g:C -> D) (xs:list A) (ys:list B) : List.map g (map2 f xs ys) = map2 (fun (a : A) (b : B) => g (f a b)) xs ys.
Proof.
  revert ys; induction xs as [|a xs IHxs]; intros ys; [reflexivity|].
  destruct ys; [reflexivity|].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma map2_fst {A B C} (f:A -> C) (xs:list A) : forall (ys:list B), length xs = length ys ->
  map2 (fun (a : A) (_ : B) => f a) xs ys = List.map f xs.
Proof.
  induction xs as [|a xs IHxs]; intros ys **; [reflexivity|].
  destruct ys; [simpl in *; discriminate|].
  simpl. rewrite IHxs by eauto. reflexivity.
Qed.

Lemma map2_flip {A B C} (f:A -> B -> C) (xs:list A) : forall (ys: list B),
   map2 (fun b a => f a b) ys xs = map2 f xs ys.
Proof.
  induction xs as [|a xs IHxs]; destruct ys; try reflexivity; [].
  simpl. rewrite IHxs. reflexivity.
Qed.

Lemma map2_snd {A B C} (f:B -> C) (xs:list A) : forall (ys:list B), length xs = length ys ->
  map2 (fun (_ : A) (b : B) => f b) xs ys = List.map f ys.
Proof. intros. rewrite map2_flip. eauto using map2_fst. Qed.

Lemma map2_map {A B C A' B'} (f:A -> B -> C) (g:A' -> A) (h:B' -> B) (xs:list A') (ys:list B')
  : map2 f (List.map g xs) (List.map h ys) = map2 (fun a b => f (g a) (h b)) xs ys.
Proof.
  revert ys; induction xs as [|a xs IHxs]; destruct ys; intros; try reflexivity; [].
  simpl. rewrite IHxs. reflexivity.
Qed.