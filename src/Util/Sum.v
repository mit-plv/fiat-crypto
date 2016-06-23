Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Definition sumwise {A B} (RA:relation A) (RB : relation B) : relation (A + B)
  := fun x y => match x, y with
                | inl x', inl y' => RA x' y'
                | inr x', inr y' => RB x' y'
                | _, _ => False
                end.

Global Instance Equivalence_sumwise {A B} {RA:relation A} {RB:relation B}
       {RA_equiv:Equivalence RA} {RB_equiv:Equivalence RB}
  : Equivalence (sumwise RA RB).
Proof.
  split; repeat intros [?|?]; simpl; trivial; destruct RA_equiv, RB_equiv; try tauto; eauto.
Qed.

Arguments sumwise {A B} _ _ _ _.
