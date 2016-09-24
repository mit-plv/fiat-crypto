Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Decidable.

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

Ltac congruence_sum_step :=
  match goal with
  | [ H : inl _ = inr _ |- _ ] => solve [ inversion H ]
  | [ H : inr _ = inl _ |- _ ] => solve [ inversion H ]
  | [ H : inl _ = inl _ |- _ ] => inversion H; clear H
  | [ H : inr _ = inr _ |- _ ] => inversion H; clear H
  end.
Ltac congruence_sum := repeat congruence_sum_step.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.
Global Instance dec_sumwise {A B RA RB} {HA : DecidableRel RA} {HB : DecidableRel RB} : DecidableRel (@sumwise A B RA RB) | 10.
Proof.
  intros [x|x] [y|y]; exact _.
Qed.
