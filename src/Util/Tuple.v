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

Fixpoint from_list' {T} (x:T) (xs:list T) : tuple' T (length xs) :=
  match xs with
  | nil => x
  | (y :: xs')%list => (from_list' y xs', x)
  end.

Definition from_list {T} (xs:list T) : tuple T (length xs) :=
  match xs as l return (tuple T (length l)) with
  | nil => tt
  | (t :: xs')%list => from_list' t xs'
  end.

Lemma to_list_from_list : forall {T} (xs:list T), to_list (length xs) (from_list xs) = xs.
Proof.
  destruct xs; auto; simpl.
  generalize dependent t.
  induction xs; auto; simpl; intros; f_equal; auto.
Qed.

Lemma length_to_list : forall {T} {n} (xs:tuple T n), length (to_list n xs) = n.
Proof.
  destruct n; auto; intros; simpl in *.
  induction n; auto; intros; simpl in *.
  destruct xs; simpl in *; eauto.
Qed.

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
