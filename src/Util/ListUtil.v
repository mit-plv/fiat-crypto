Require Import List.
Require Import Omega.
Require Import Arith.Peano_dec.

Ltac nth_tac' := 
  intros; simpl in *; unfold error,value in *; repeat progress (match goal with
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

Lemma nth_error_length_error : forall A i (xs:list A), nth_error xs i = None ->
  i >= length xs.
Proof.
  induction i; destruct xs; nth_tac'; try specialize (IHi _ H); omega.
Qed.

Ltac nth_tac := 
  repeat progress (try nth_tac'; try (match goal with
    | [ H: nth_error (map _ _) _ = Some _ |- _ ] => destruct (nth_error_map _ _ _ _ _ _ H); clear H
    | [ H: nth_error (seq _ _) _ = Some _ |- _ ] => rewrite nth_error_seq in H
    | [H: nth_error _ _ = None |- _ ] => specialize (nth_error_length_error _ _ _ H); intro; clear H
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
