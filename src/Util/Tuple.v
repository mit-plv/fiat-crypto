Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Crypto.Util.Decidable.

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

Lemma length_to_list : forall {T} {n} (xs:tuple T n), length (to_list n xs) = n.
Proof.
  destruct n; auto; intros; simpl in *.
  induction n; auto; intros; simpl in *.
  destruct xs; simpl in *; eauto.
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

Definition on_tuple2 {A B C} (f : list A -> list B -> list C) {a b c : nat}
           (Hlength : forall la lb, length la = a -> length lb = b -> length (f la lb) = c)
           (ta:tuple A a) (tb:tuple B b) : tuple C c
  := from_list c (f (to_list a ta) (to_list b tb))
               (Hlength (to_list a ta) (to_list b tb) (length_to_list ta) (length_to_list tb)).

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
Qed.

Global Instance dec_fieldwise {A RA} {HA : DecidableRel RA} {n} : DecidableRel (@fieldwise A A n RA) | 10.
Proof.
  destruct n; unfold fieldwise; exact _.
Qed.
