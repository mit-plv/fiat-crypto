Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Fixpoint tuple' n T : Type :=
  match n with
  | O => T
  | S n' => (tuple' n' T * T)%type
  end.

Definition tuple n T : Type :=
  match n with
    | O => unit
    | S n' => tuple' n' T
  end.

Fixpoint fieldwise' {A B} (n:nat) (R:A->B->Prop) (a:tuple' n A) (b:tuple' n B) {struct n} : Prop.
  destruct n; simpl @tuple' in *.
  { exact (R a b). }
  { exact (R (snd a) (snd b) /\ fieldwise' _ _ n R (fst a) (fst b)). }
Defined.

Definition fieldwise {A B} (n:nat) (R:A->B->Prop) (a:tuple n A) (b:tuple n B) : Prop.
  destruct n; simpl @tuple in *.
  { exact True. }
  { exact (fieldwise' _ R a b). }
Defined.

Global Instance Equivalence_fieldwise' {A} {R:relation A} {R_equiv:Equivalence R} {n:nat}:
    Equivalence (fieldwise' n R).
Proof.
  induction n; [solve [auto]|].
  simpl; constructor; repeat intro; intuition eauto.
Qed.

Global Instance Equivalence_fieldwise {A} {R:relation A} {R_equiv:Equivalence R} {n:nat}:
    Equivalence (fieldwise n R).
Proof.
  destruct n; (repeat constructor || apply Equivalence_fieldwise').
Qed.

Arguments fieldwise' {A B n} _ _ _.
Arguments fieldwise {A B n} _ _ _.