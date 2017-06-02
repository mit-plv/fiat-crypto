
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(***********************************************************************
      Root.v

      Proof that a polynomial has at most n roots
************************************************************************)
Require Import ZArith.
Require Import List.
Require Import UList.
Require Import Tactic.
Require Import Permutation.

Open Scope Z_scope.

Section Root.

Variable A: Set.
Variable P: A -> Prop.
Variable plus mult: A -> A -> A.
Variable op: A -> A.
Variable zero one: A.


Let pol := list A.

Definition toA z :=
match z with
  Z0  => zero
| Zpos p => iter_pos _ (plus one) zero p
| Zneg p => op (iter_pos _ (plus one) zero p)
end.

Fixpoint eval (p: pol) (x: A) {struct p} : A :=
match p with
  nil => zero
| a::p1 => plus a (mult x (eval p1 x))
end.

Fixpoint div (p: pol) (x: A) {struct p} : pol * A :=
match p with
  nil => (nil, zero)
| a::nil => (nil, a)
| a::p1 =>
                     (snd (div p1 x)::fst (div p1 x),
                     (plus a (mult  x (snd (div p1 x)))))
end.

Hypothesis Pzero: P zero.
Hypothesis Pplus: forall x y, P x -> P y -> P (plus x y).
Hypothesis Pmult: forall x y, P x -> P y -> P (mult x y).
Hypothesis Pop: forall x, P x -> P (op x).
Hypothesis plus_zero: forall a, P a -> plus zero a = a.
Hypothesis plus_comm: forall a b, P a -> P b -> plus a b = plus b a.
Hypothesis plus_assoc: forall a b c, P a -> P b -> P c -> plus a (plus b c) = plus (plus a b) c.
Hypothesis mult_zero: forall a, P a -> mult zero a = zero.
Hypothesis mult_comm: forall a b, P a -> P b -> mult a b = mult b a.
Hypothesis mult_assoc: forall a b c, P a -> P b -> P c -> mult a (mult b c) = mult (mult a b) c.
Hypothesis mult_plus_distr: forall a b c, P a -> P b -> P c -> mult a (plus b c) = plus (mult a b) (mult a c).
Hypothesis plus_op_zero: forall a, P a -> plus a (op a) = zero.
Hypothesis mult_integral: forall a b, P a -> P b -> mult a b = zero -> a = zero \/ b = zero.
(* Not necessary in Set just handy *)
Hypothesis A_dec: forall a b: A, {a = b} + {a <> b}.

Theorem eval_P: forall p a, P a -> (forall i, In i p -> P i) -> P (eval p a).
intros p a Pa; elim p; simpl; auto with datatypes.
intros a1 l1 Rec H; apply Pplus; auto.
Qed.

Hint Resolve eval_P.

Theorem div_P: forall p a, P a -> (forall i, In i p -> P i) -> (forall i, In i (fst (div p a)) -> P i) /\ P (snd (div p a)).
intros p a Pa; elim p; auto with datatypes.
intros a1 l1; case l1.
simpl; intuition.
intros a2 p2 Rec Hi; split.
case Rec; auto with datatypes.
intros H H1 i.
replace (In i (fst (div (a1 :: a2 :: p2) a))) with
 (snd (div (a2::p2) a) = i \/  In i (fst (div (a2::p2) a))); auto.
intros [Hi1 | Hi1]; auto.
rewrite <- Hi1; auto.
change ( P (plus a1 (mult  a (snd (div (a2::p2) a))))); auto with datatypes.
apply Pplus; auto with datatypes.
apply Pmult; auto with datatypes.
case Rec; auto with datatypes.
Qed.


Theorem div_correct:
  forall p x y, P x -> P y -> (forall i, In i p -> P i) -> eval p y = plus (mult (eval (fst (div p x)) y) (plus y (op x))) (snd (div p x)).
intros p x y; elim p; simpl.
intros; rewrite mult_zero; try rewrite plus_zero; auto.
intros a l; case l; simpl; auto.
intros _ px py pa; rewrite (fun x => mult_comm x zero); repeat rewrite mult_zero; try apply plus_comm; auto.
intros a1 l1.
generalize (div_P (a1::l1) x); simpl.
match goal with |-  context[fst ?A]   => case A end; simpl.
intros q r Hd Rec px py pi.
assert (pr: P r).
case Hd; auto.
assert (pa1: P a1).
case Hd; auto.
assert (pey: P (eval q y)).
apply eval_P; auto.
case Hd; auto.
rewrite Rec; auto with datatypes.
rewrite (fun x y => plus_comm x (plus a y)); try rewrite <- plus_assoc; auto.
apply f_equal2 with (f := plus); auto.
repeat rewrite mult_plus_distr; auto.
repeat (rewrite (fun x y => (mult_comm (plus x y))) || rewrite mult_plus_distr); auto.
rewrite (fun x => (plus_comm  x (mult y r))); auto.
repeat rewrite  plus_assoc; try apply f_equal2 with (f := plus); auto.
2: repeat rewrite mult_assoc; try rewrite (fun y => mult_comm y (op x));
    repeat rewrite mult_assoc; auto.
rewrite (fun z => (plus_comm  z (mult (op x) r))); auto.
repeat rewrite  plus_assoc; try apply f_equal2 with (f := plus); auto.
2: apply f_equal2 with (f := mult); auto.
repeat rewrite (fun x => mult_comm x r); try rewrite <- mult_plus_distr; auto.
rewrite (plus_comm (op x)); try rewrite plus_op_zero; auto.
rewrite (fun x => mult_comm x zero); try rewrite mult_zero; try rewrite plus_zero; auto.
Qed.

Theorem div_correct_factor:
  forall p a, (forall i, In i p -> P i) -> P a ->
       eval p a = zero -> forall x,  P x -> eval p x =  (mult (eval (fst (div p a)) x) (plus x (op a))).
intros p a Hp Ha H x px.
case (div_P p a); auto; intros Hd1 Hd2.
rewrite (div_correct p a x); auto.
generalize (div_correct p a a).
rewrite plus_op_zero; try rewrite (fun x => mult_comm x zero); try rewrite mult_zero; try rewrite plus_zero; try rewrite H; auto.
intros H1; rewrite <- H1; auto.
rewrite (fun x => plus_comm x zero); auto.
Qed.

Theorem length_decrease: forall p x, p <> nil -> (length (fst (div p x)) < length p)%nat.
intros p x; elim p; simpl; auto.
intros H1; case H1; auto.
intros a l; case l; simpl; auto.
intros a1 l1.
match goal with |-  context[fst ?A]   => case A end; simpl; auto with zarith.
intros p1 _ H H1.
apply lt_n_S; apply H; intros; discriminate.
Qed.

Theorem root_max:
forall p l, ulist l -> (forall i, In i p -> P i) -> (forall i, In i l -> P i) ->
  (forall x, In x l -> eval p x = zero) -> (length p <= length l)%nat -> forall x, P x -> eval p x = zero.
intros p l; generalize p; elim l; clear l p; simpl; auto.
intros p; case p; simpl; auto.
intros a p1 _ _ _ _ H; contradict H; auto with arith.
intros a p1 Rec p; case p.
simpl; auto.
intros a1 p2 H H1 H2 H3 H4 x px.
assert (Hu: eval (a1 :: p2) a = zero); auto with datatypes.
rewrite (div_correct_factor (a1 :: p2) a); auto with datatypes.
match goal with |- mult ?X _ = _ => replace X with zero end; try apply mult_zero; auto.
apply sym_equal; apply Rec; auto with datatypes.
apply ulist_inv with (1 := H).
intros i Hi; case (div_P (a1 :: p2) a); auto.
intros x1 H5; case (mult_integral (eval (fst (div (a1 :: p2) a)) x1) (plus x1 (op a))); auto.
apply eval_P; auto.
intros i Hi; case (div_P (a1 :: p2) a); auto.
rewrite <- div_correct_factor; auto.
intros H6; case (ulist_app_inv _ (a::nil) p1 x1); simpl; auto.
left.
apply trans_equal with (plus zero x1); auto.
rewrite <- (plus_op_zero a); try rewrite <- plus_assoc; auto.
rewrite (fun x => plus_comm (op x)); try rewrite H6; try rewrite plus_comm; auto.
apply sym_equal; apply plus_zero; auto.
apply lt_n_Sm_le;apply lt_le_trans with (length (a1 :: p2)); auto with zarith.
apply length_decrease; auto with datatypes.
Qed.

Theorem root_max_is_zero:
forall p l, ulist l -> (forall i, In i p -> P i) -> (forall i, In i l -> P i) ->
  (forall x, In x l -> eval p x = zero) -> (length p <= length l)%nat -> forall x, (In x p) -> x = zero.
intros p l; generalize p; elim l; clear l p; simpl; auto.
intros p; case p; simpl; auto.
intros _ _ _  _ _ x H; case H.
intros a p1 _ _ _ _ H; contradict H; auto with arith.
intros a p1 Rec p; case p.
simpl; auto.
intros _ _ _ _ _ x H; case H.
simpl; intros a1 p2 H H1 H2 H3 H4 x H5.
assert (Ha1: a1 = zero).
assert (Hu: (eval (a1::p2) zero = zero)).
apply root_max with (l := a :: p1); auto.
rewrite <- Hu; simpl; rewrite mult_zero; try rewrite plus_comm; sauto.
case H5; clear H5; intros H5; subst; auto.
apply Rec with p2; auto with arith.
apply ulist_inv with (1 := H).
intros x1 Hx1.
case (In_dec A_dec zero p1); intros Hz.
case (in_permutation_ex _ zero p1); auto; intros p3 Hp3.
apply root_max with (l := a::p3); auto.
apply ulist_inv with zero.
apply ulist_perm with (a::p1); auto.
apply permutation_trans with (a:: (zero:: p3)); auto.
apply permutation_skip; auto.
apply permutation_sym; auto.
simpl; intros x2 [Hx2 | Hx2]; subst; auto.
apply H2; right; apply permutation_in with (1 := Hp3); auto with datatypes.
simpl; intros x2 [Hx2 | Hx2]; subst.
case (mult_integral x2 (eval p2 x2)); auto.
rewrite <- H3 with x2; sauto.
rewrite plus_zero; auto.
intros H6; case (ulist_app_inv _ (x2::nil) p1 x2) ; auto with datatypes.
rewrite H6; apply permutation_in with (1 := Hp3); auto with datatypes.
case (mult_integral x2 (eval p2 x2)); auto.
apply H2; right; apply permutation_in with (1 := Hp3); auto with datatypes.
apply eval_P; auto.
apply H2; right; apply permutation_in with (1 := Hp3); auto with datatypes.
rewrite <- H3 with x2; sauto; try right.
apply sym_equal; apply plus_zero; auto.
apply Pmult; auto.
apply H2; right; apply permutation_in with (1 := Hp3); auto with datatypes.
apply eval_P; auto.
apply H2; right; apply permutation_in with (1 := Hp3); auto with datatypes.
apply permutation_in with (1 := Hp3); auto with datatypes.
intros H6; case (ulist_app_inv _ (zero::nil) p3 x2) ; auto with datatypes.
simpl; apply ulist_perm with (1:= (permutation_sym _ _ _ Hp3)).
apply ulist_inv with (1 := H).
rewrite H6; auto with datatypes.
replace (length (a :: p3))  with (length (zero::p3)); auto.
rewrite permutation_length with (1 := Hp3); auto with arith.
case (mult_integral x1 (eval p2 x1)); auto.
rewrite <- H3 with x1; sauto; try right.
apply sym_equal; apply plus_zero; auto.
intros HH; case Hz; rewrite <- HH; auto.
Qed.

End Root.
