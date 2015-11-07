Require Import List.
Require Import Omega.
Require Import Arith.Peano_dec.
Require Import VerdiTactics.

Ltac boring :=
  simpl; intuition;
  repeat match goal with
           | [ H : _ |- _ ] => rewrite H; clear H
           | _ => progress autounfold in *
           | _ => progress try autorewrite with core
           | _ => progress simpl in *
           | _ => progress intuition
         end; eauto.

Lemma nth_error_nil_error : forall {A} n, nth_error (@nil A) n = None.
Proof.
intros. induction n; boring.
Qed.

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
  induction i; destruct len; nth_tac'; erewrite IHi; nth_tac'.
Qed.

Lemma nth_error_error_length : forall A i (xs:list A), nth_error xs i = None ->
  i >= length xs.
Proof.
  induction i; destruct xs; nth_tac'; try specialize (IHi _ H); omega.
Qed.

Lemma nth_error_value_length : forall A i (xs:list A) x, nth_error xs i = Some x ->
  i < length xs.
Proof.
  induction i; destruct xs; nth_tac'; try specialize (IHi _ _ H); omega.
Qed.

Lemma nth_error_length_error : forall A i (xs:list A),
  i >= length xs ->
  nth_error xs i = None.
Proof.
  induction i; destruct xs; nth_tac'; rewrite IHi by omega; auto.
Qed.
Hint Resolve nth_error_length_error.

Lemma map_nth_default : forall (A B : Type) (f : A -> B) n x y l,
  (n < length l) -> nth_default y (map f l) n = f (nth_default x l n).
Proof.
  intros.
  unfold nth_default.
  erewrite map_nth_error.
  reflexivity.
  nth_tac'.
  pose proof (nth_error_error_length A n l H0).
  omega.  
Qed.

Ltac nth_tac := 
  repeat progress (try nth_tac'; try (match goal with
    | [ H: nth_error (map _ _) _ = Some _ |- _ ] => destruct (nth_error_map _ _ _ _ _ _ H); clear H
    | [ H: nth_error (seq _ _) _ = Some _ |- _ ] => rewrite nth_error_seq in H
    | [H: nth_error _ _ = None |- _ ] => specialize (nth_error_error_length _ _ _ H); intro; clear H
  end)).

Lemma app_cons_app_app : forall T xs (y:T) ys, xs ++ y :: ys = (xs ++ (y::nil)) ++ ys.
Proof.
  induction xs; simpl; repeat match goal with
           | [ H : _ |- _ ] => rewrite H; clear H
           | _ => progress intuition
         end; eauto.
Qed.

(* xs[n] := x *)
Fixpoint set_nth {T} n x (xs:list T) {struct n} :=
	match n with
	| O => match xs with
				 | nil => nil
				 | x'::xs' => x::xs'
				 end
	| S n' =>  match xs with
				 | nil => nil
				 | x'::xs' => x'::set_nth n' x xs'
				 end
  end.

Lemma nth_set_nth : forall m {T} (xs:list T) (n:nat) (x x':T),
  nth_error (set_nth m x xs) n =
  if eq_nat_dec n m
  then (if lt_dec n (length xs) then Some x else None)
  else nth_error xs n.
Proof.
	induction m.

	destruct n, xs; auto.

	intros; destruct xs, n; auto.
	simpl; unfold error; match goal with
		[ |- None = if ?x then None else None ] => destruct x
	end; auto.

	simpl nth_error; erewrite IHm by auto; clear IHm.
	destruct (eq_nat_dec n m), (eq_nat_dec (S n) (S m)); nth_tac.
Qed.

Lemma set_nth_equiv_splice: forall {T} n x (xs:list T),
  set_nth n x xs = 
  if lt_dec n (length xs)
  then firstn n xs ++ x :: skipn (S n) xs
  else xs.
Proof.
  induction n; destruct xs; intros; simpl in *;
    try (rewrite IHn; clear IHn); auto.
  destruct (lt_dec n (length xs)), (lt_dec (S n) (S (length xs))); try omega; trivial.
Qed.

Lemma combine_set_nth : forall {A B} n (x:A) xs (ys:list B),
  combine (set_nth n x xs) ys =
    match nth_error ys n with
    | None => combine xs ys
    | Some y => set_nth n (x,y) (combine xs ys)
    end.
Proof.
  (* TODO(andreser): this proof can totally be automated, but requires writing ltac that vets multiple hypotheses at once *)
  induction n, xs, ys; nth_tac; try rewrite IHn; nth_tac; 
    try (f_equal; specialize (IHn x xs ys ); rewrite H in IHn; rewrite <- IHn);
    try (specialize (nth_error_value_length _ _ _ _ H); omega).
  assert (Some b0=Some b1) as HA by (rewrite <-H, <-H0; auto).
  injection HA; intros; subst; auto.
Qed.

Lemma nth_value_index : forall {T} i xs (x:T),
  nth_error xs i = Some x -> In i (seq 0 (length xs)).
Proof.
  induction i; destruct xs; nth_tac; right.
  rewrite <- seq_shift; apply in_map; eapply IHi; eauto.
Qed.

Lemma nth_error_app : forall {T} n (xs ys:list T), nth_error (xs ++ ys) n =
  if lt_dec n (length xs)
  then nth_error xs n
  else nth_error ys (n - length xs).
Proof.
  induction n; destruct xs; nth_tac;
    rewrite IHn; destruct (lt_dec n (length xs)); trivial; omega.
Qed.

Lemma nth_default_app : forall {T} n x (xs ys:list T), nth_default x (xs ++ ys) n =
  if lt_dec n (length xs)
  then nth_default x xs n
  else nth_default x ys (n - length xs).
Proof.
  intros.
  unfold nth_default.
  rewrite nth_error_app.
  destruct (lt_dec n (length xs)); auto.
Qed.

Lemma combine_truncate_r : forall {A} (xs ys : list A),
  combine xs ys = combine xs (firstn (length xs) ys).
Proof.
  induction xs; destruct ys; boring.
Qed.

Lemma combine_truncate_l : forall {A} (xs ys : list A),
  combine xs ys = combine (firstn (length ys) xs) ys.
Proof.
  induction xs; destruct ys; boring.
Qed.

Lemma firstn_nil : forall {A} n, firstn n nil = @nil A.
Proof.
  destruct n; auto.
Qed.

Lemma skipn_nil : forall {A} n, skipn n nil = @nil A.
Proof.
  destruct n; auto.
Qed.

Lemma firstn_app : forall A (l l': list A), firstn (length l) (l ++ l') = l.
Proof.
  intros.
  induction l; simpl; auto.
  f_equal; auto.
Qed.

Lemma skipn_app : forall A (l l': list A), skipn (length l) (l ++ l') = l'.
Proof.
  intros.
  induction l; simpl; auto.
Qed.
