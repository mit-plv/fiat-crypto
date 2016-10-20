Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Export Crypto.Util.FixCoqMistakes.

Fixpoint tuple' T n : Type :=
  match n with
  | O => T
  | S n' => (tuple' T n' * T)%type
  end.

Definition tuple T n : Type :=
  match n with
  | O => unit
  | S n' => tuple' T n'
  end.

Fixpoint to_list' {T} (n:nat) {struct n} : tuple' T n -> list T :=
  match n with
  | 0 => fun x => (x::nil)%list
  | S n' => fun xs : tuple' T (S n') => let (xs', x) := xs in (x :: to_list' n' xs')%list
  end.

Definition to_list {T} (n:nat) : tuple T n -> list T :=
  match n with
  | 0 => fun _ => nil
  | S n' => fun xs : tuple T (S n') => to_list' n' xs
  end.

Program Fixpoint from_list' {T} (y:T) (n:nat) (xs:list T) : length xs = n -> tuple' T n :=
  match n return _ with
  | 0 =>
    match xs return (length xs = 0 -> tuple' T 0) with
    | nil => fun _ => y
    | _ => _ (* impossible *)
    end
  | S n' =>
    match xs return (length xs = S n' -> tuple' T (S n')) with
    | cons x xs' => fun _ => (from_list' x n' xs' _, y)
    | _ => _ (* impossible *)
    end
  end.

Program Definition from_list {T} (n:nat) (xs:list T) : length xs = n -> tuple T n :=
match n return _ with
| 0 =>
    match xs return (length xs = 0 -> tuple T 0) with
    | nil => fun _ : 0 = 0 => tt
    | _ => _ (* impossible *)
    end
| S n' =>
    match xs return (length xs = S n' -> tuple T (S n')) with
    | cons x xs' => fun _ => from_list' x n' xs' _
    | _ => _ (* impossible *)
    end
end.

Lemma to_list_from_list : forall {T} (n:nat) (xs:list T) pf, to_list n (from_list n xs pf) = xs.
Proof.
  destruct xs; simpl; intros; subst; auto.
  generalize dependent t. simpl in *.
  induction xs; simpl in *; intros; congruence.
Qed.

Lemma length_to_list' T n t : length (@to_list' T n t) = S n.
Proof. induction n; simpl in *; trivial; destruct t; simpl; congruence. Qed.

Lemma length_to_list : forall {T} {n} (xs:tuple T n), length (to_list n xs) = n.
Proof.
  destruct n; [ reflexivity | apply length_to_list' ].
Qed.

Lemma from_list'_to_list' : forall T n (xs:tuple' T n),
    forall x xs' pf, to_list' n xs = cons x xs' ->
      from_list' x n xs' pf = xs.
Proof.
  induction n; intros.
  { simpl in *. injection H; clear H; intros; subst. congruence. }
  { destruct xs eqn:Hxs;
    destruct xs' eqn:Hxs';
    injection H; clear H; intros; subst; try discriminate.
    simpl. f_equal. eapply IHn. assumption. }
Qed.

Lemma from_list_to_list : forall {T n} (xs:tuple T n) pf, from_list n (to_list n xs) pf = xs.
Proof.
  destruct n; auto; intros; simpl in *.
  { destruct xs; auto. }
  { destruct (to_list' n xs) eqn:H; try discriminate.
    eapply from_list'_to_list'; assumption. }
Qed.

Definition on_tuple {A B} (f:list A -> list B)
           {n m:nat} (H:forall xs, length xs = n -> length (f xs) = m)
           (xs:tuple A n) : tuple B m :=
  from_list m (f (to_list n xs))
            (H (to_list n xs) (length_to_list xs)).

Definition map {n A B} (f:A -> B) (xs:tuple A n) : tuple B n
  := on_tuple (List.map f) (fun _ => eq_trans (map_length _ _)) xs.

Definition on_tuple2 {A B C} (f : list A -> list B -> list C) {a b c : nat}
           (Hlength : forall la lb, length la = a -> length lb = b -> length (f la lb) = c)
           (ta:tuple A a) (tb:tuple B b) : tuple C c
  := from_list c (f (to_list a ta) (to_list b tb))
               (Hlength (to_list a ta) (to_list b tb) (length_to_list ta) (length_to_list tb)).

Definition map2 {n A B C} (f:A -> B -> C) (xs:tuple A n) (ys:tuple B n) : tuple C n
  := on_tuple2 (map2 f) (fun la lb pfa pfb => eq_trans (@map2_length _ _ _ _ la lb) (eq_trans (f_equal2 _ pfa pfb) (Min.min_idempotent _))) xs ys.

Fixpoint fieldwise' {A B} (n:nat) (R:A->B->Prop) (a:tuple' A n) (b:tuple' B n) {struct n} : Prop.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (R (snd a) (snd b) /\ fieldwise' _ _ n R (fst a) (fst b)). }
Defined.

Definition fieldwise {A B} (n:nat) (R:A->B->Prop) (a:tuple A n) (b:tuple B n) : Prop.
  destruct n; simpl @tuple in *.
  { exact True. }
  { exact (fieldwise' _ R a b). }
Defined.

Global Instance Equivalence_fieldwise' {A} {R:relation A} {R_equiv:Equivalence R} {n:nat}:
    Equivalence (fieldwise' n R).
Proof.
  induction n as [|? IHn]; [solve [auto]|].
  (* could use [dintuition] in 8.5 only, and remove the [destruct] *)
  destruct IHn, R_equiv; simpl; constructor; repeat intro; intuition eauto.
Qed.

Global Instance Equivalence_fieldwise {A} {R:relation A} {R_equiv:Equivalence R} {n:nat}:
    Equivalence (fieldwise n R).
Proof.
  destruct n; (repeat constructor || apply Equivalence_fieldwise').
Qed.

Arguments fieldwise' {A B n} _ _ _.
Arguments fieldwise {A B n} _ _ _.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.
Global Instance dec_fieldwise' {A RA} {HA : DecidableRel RA} {n} : DecidableRel (@fieldwise' A A n RA) | 10.
Proof.
  induction n; simpl @fieldwise'.
  { exact _. }
  { intros ??.
    exact _. }
Defined.

Global Instance dec_fieldwise {A RA} {HA : DecidableRel RA} {n} : DecidableRel (@fieldwise A A n RA) | 10.
Proof.
  destruct n; unfold fieldwise; exact _.
Defined.

Fixpoint fieldwiseb' {A B} (n:nat) (R:A->B->bool) (a:tuple' A n) (b:tuple' B n) {struct n} : bool.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (R (snd a) (snd b) && fieldwiseb' _ _ n R (fst a) (fst b))%bool. }
Defined.

Definition fieldwiseb {A B} (n:nat) (R:A->B->bool) (a:tuple A n) (b:tuple B n) : bool.
  destruct n; simpl @tuple in *.
  { exact true. }
  { exact (fieldwiseb' _ R a b). }
Defined.

Arguments fieldwiseb' {A B n} _ _ _.
Arguments fieldwiseb {A B n} _ _ _.

Lemma fieldwiseb'_fieldwise' :forall {A B} n R Rb
                                   (a:tuple' A n) (b:tuple' B n),
  (forall a b, Rb a b = true <-> R a b) ->
  (fieldwiseb' Rb a b = true <-> fieldwise' R a b).
Proof.
  intros.
  revert n a b;
  induction n; intros; simpl @tuple' in *;
    simpl fieldwiseb'; simpl fieldwise'; auto.
  cbv beta.
  rewrite Bool.andb_true_iff.
  f_equiv; auto.
Qed.

Lemma fieldwiseb_fieldwise :forall {A B} n R Rb
                                   (a:tuple A n) (b:tuple B n),
  (forall a b, Rb a b = true <-> R a b) ->
  (fieldwiseb Rb a b = true <-> fieldwise R a b).
Proof.
  intros; destruct n; simpl @tuple in *;
    simpl @fieldwiseb; simpl @fieldwise; try tauto.
  auto using fieldwiseb'_fieldwise'.
Qed.


Fixpoint from_list_default' {T} (d y:T) (n:nat) (xs:list T) : tuple' T n :=
  match n return tuple' T n with
  | 0 => y (* ignore high digits *)
  | S n' =>
         match xs return _ with
         | cons x xs' => (from_list_default' d x n' xs', y)
         | nil => (from_list_default' d d n' nil, y)
         end
  end.

Definition from_list_default {T} d (n:nat) (xs:list T) : tuple T n :=
match n return tuple T n with
| 0 => tt
| S n' =>
    match xs return _ with
    | cons x xs' => (from_list_default' d x n' xs')
    | nil => (from_list_default' d d n' nil)
    end
end.

Lemma from_list_default'_eq : forall {T} (d : T) xs n y pf,
  from_list_default' d y n xs = from_list' y n xs pf.
Proof.
  induction xs; destruct n; intros; simpl in *;
    solve [ congruence (* 8.5 *)
          | erewrite IHxs; reflexivity ]. (* 8.4 *)
Qed.

Lemma from_list_default_eq : forall {T} (d : T) xs n pf,
  from_list_default d n xs = from_list n xs pf.
Proof.
  induction xs; destruct n; intros; try solve [simpl in *; congruence].
  apply from_list_default'_eq.
Qed.

Fixpoint function R T n : Type :=
  match n with
  | O => R
  | S n' => T -> function R T n'
  end.

Fixpoint apply' {R T} (n:nat) : (T -> function R T n) -> tuple' T n -> R :=
  match n with
  | 0 => id
  | S n' => fun f x => apply' n' (f (snd x)) (fst x)
  end.

Definition apply {R T} (n:nat) : function R T n -> tuple T n -> R :=
  match n with
  | O => fun r _ => r
  | S n' => fun f x =>  apply' n' f x
  end.

Require Import Coq.Lists.SetoidList.

Lemma fieldwise_to_list_iff : forall {T n} R (s t : tuple T n),
    (fieldwise R s t <-> Forall2 R (to_list _ s) (to_list _ t)).
Proof.
  induction n; split; intros.
  + constructor.
  + cbv [fieldwise]. auto.
  + destruct n; cbv [tuple to_list fieldwise] in *.
    - cbv [to_list']; auto.
    - simpl in *. destruct s,t; cbv [fst snd] in *.
      constructor; intuition auto.
      apply IHn; auto.
  + destruct n; cbv [tuple to_list fieldwise] in *.
    - cbv [fieldwise']; auto.
      cbv [to_list'] in *; inversion H; auto.
    - simpl in *. destruct s,t; cbv [fst snd] in *.
      inversion H; subst.
      split; try assumption.
      apply IHn; auto.
Qed.


Require Import Crypto.Util.ListUtil. (* To initialize [distr_length] database *)
Hint Rewrite length_to_list' @length_to_list : distr_length.
