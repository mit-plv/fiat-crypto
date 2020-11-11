Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Bool.
Import ListNotations. Open Scope bool_scope.

Lemma fold_left_orb_true ls
  : List.fold_left orb ls true = true.
Proof. induction ls as [|?? IHls]; [ reflexivity | assumption ]. Qed.
Lemma fold_left_orb_pull ls v
  : List.fold_left orb ls v = orb v (List.fold_left orb ls false).
Proof. destruct v; [ apply fold_left_orb_true | reflexivity ]. Qed.

Lemma nth_error_true_fold_left_orb_true {n ls b}
  : nth_error ls n = Some true -> fold_left orb ls b = true.
Proof.
  revert ls b; induction n, ls as [|[] ?]; cbn; try congruence; intro b'; destruct b'; cbn [orb]; try congruence; auto using fold_left_orb_true.
Qed.

Lemma fold_left_orb_true_or_ind_gen {ls b} (P Q : bool -> Prop)
      (H : forall b, P b -> Q b)
  : Q b -> fold_right (fun b res => P b -> res) (Q (fold_left orb ls b)) ls.
Proof.
  revert Q H b; induction ls; cbn; eauto; intros.
  apply IHls; eauto.
  destruct b; cbn; eauto.
Qed.

Lemma fold_left_orb_true_or_ind {ls b} (P : bool -> Prop)
  : fold_right (fun b res => P b -> res) (P b -> P (fold_left orb ls b)) ls.
Proof.
  apply @fold_left_orb_true_or_ind_gen with (P:=P) (Q:=fun v => _ -> P v); auto.
Qed.

Ltac induction_fold_left_orb_true ls b :=
  let fold_right_u := (eval cbv [fold_right] in (@fold_right)) in
  let lem := (eval cbv beta iota in
                 (@id (forall P : bool -> Prop, fold_right_u _ _ (fun b' res => P b' -> res) (P b -> P (fold_left orb ls b)) ls)
                      (@fold_left_orb_true_or_ind ls b))) in
  induction (fold_left orb ls b) using lem.

Fixpoint fold_andb_map {A B} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B)
  : bool
  := match ls1, ls2 with
     | nil, nil => true
     | nil, _ => false
     | cons x xs, cons y ys => andb (f x y) (@fold_andb_map A B f xs ys)
     | cons _ _, _ => false
     end.
Lemma fold_andb_map_map {A B C} f g ls1 ls2
  : @fold_andb_map A B f ls1 (@List.map C _ g ls2)
    = fold_andb_map (fun a b => f a (g b)) ls1 ls2.
Proof. revert ls1 ls2; induction ls1, ls2; cbn; congruence. Qed.

Lemma fold_andb_map_map1 {A B C} f g ls1 ls2
  : @fold_andb_map A B f (@List.map C _ g ls1) ls2
    = fold_andb_map (fun a b => f (g a) b) ls1 ls2.
Proof. revert ls1 ls2; induction ls1, ls2; cbn; congruence. Qed.

Lemma fold_andb_map_length A B f ls1 ls2
      (H : @fold_andb_map A B f ls1 ls2 = true)
  : length ls1 = length ls2.
Proof.
  revert ls1 ls2 H; induction ls1, ls2; cbn; intros;
    rewrite ?Bool.andb_true_iff in *;
    f_equal; try congruence; intuition auto.
Qed.

Global Instance fold_andb_map_Proper {A B}
  : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@fold_andb_map A B).
Proof.
  unfold pointwise_relation.
  intros f g H ls1 y ? ls2 z ?; subst y z.
  revert ls2; induction ls1, ls2; cbn; try reflexivity.
  apply f_equal2; eauto.
Qed.

Lemma fold_andb_map_iff A B R ls1 ls2
  : (@fold_andb_map A B R ls1 ls2 = true)
    <-> (length ls1 = length ls2
         /\ (forall v, List.In v (List.combine ls1 ls2) -> R (fst v) (snd v) = true)).
Proof.
  revert ls2; induction ls1 as [|x xs IHxs], ls2 as [|y ys]; cbn; try solve [ intuition (congruence || auto) ]; [].
  rewrite Bool.andb_true_iff, IHxs.
  split; intros [H0 H1]; split; auto;
    intuition (congruence || (subst; auto)).
  apply (H1 (_, _)); auto.
Qed.

Lemma fold_andb_map_snoc A B f x xs y ys
  : @fold_andb_map A B f (xs ++ [x]) (ys ++ [y]) = @fold_andb_map A B f xs ys && f x y.
Proof.
  clear.
  revert ys; induction xs as [|x' xs'], ys as [|y' ys']; cbn;
    rewrite ?Bool.andb_true_r, ?Bool.andb_false_r;
    try (destruct ys'; cbn; rewrite Bool.andb_false_r);
    try (destruct xs'; cbn; rewrite Bool.andb_false_r);
    try reflexivity.
  rewrite IHxs', Bool.andb_assoc; reflexivity.
Qed.

Module Thunked.
  Import Bool.Thunked.
  Lemma fold_left_orb_true ls b
    : b tt = Datatypes.true -> List.fold_left orb ls b tt = Datatypes.true.
  Proof.
    revert b; induction ls as [|?? IHls]; cbn; auto.
    intros ? H; apply IHls; cbv [orb]; rewrite H; reflexivity.
  Qed.
  Lemma nth_error_true_fold_left_orb_true {n ls b}
    : option_map (fun f => f tt) (nth_error ls n) = Some Datatypes.true -> fold_left orb ls b tt = Datatypes.true.
  Proof.
    revert ls b; induction n, ls as [|v ?]; cbn; auto.
    all: intros b H; inversion H; auto using fold_left_orb_true.
    etransitivity; [ apply fold_left_orb_true; cbv [orb] | congruence ].
    edestruct b; cbn; congruence.
  Qed.

  Lemma fold_left_orb_true_or_ind_gen {ls b} (P Q : Datatypes.bool -> Prop)
        (H : forall b, P b -> Q b)
    : Q (b tt) -> fold_right (fun b res => P (b tt) -> res) (Q (fold_left orb ls b tt)) ls.
  Proof.
    revert Q H b; induction ls; cbn; eauto; intros.
    apply IHls; eauto; cbv [orb].
    destruct b; cbn; eauto.
  Qed.

  Lemma fold_left_orb_true_or_ind {ls b} (P : Datatypes.bool -> Prop)
    : fold_right (fun b res => P (b tt) -> res) (P (b tt) -> P (fold_left orb ls b tt)) ls.
  Proof.
    apply @fold_left_orb_true_or_ind_gen with (P:=P) (Q:=fun v => _ -> P v); auto.
  Qed.

  Ltac induction_fold_left_orb_true ls b :=
    let fold_right_u := (eval cbv [fold_right] in (@fold_right)) in
    let lem := (eval cbv beta iota in
                   (@id (forall P : Datatypes.bool -> Prop, fold_right_u _ _ (fun b' res => P (b' tt) -> res) (P (b tt) -> P (fold_left orb ls b tt)) ls)
                        (@fold_left_orb_true_or_ind ls b))) in
    induction (fold_left orb ls b tt) using lem.
End Thunked.
