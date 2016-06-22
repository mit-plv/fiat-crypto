(** Typeclass for decidable propositions *)

Require Import Coq.Logic.Eqdep_dec.

Local Open Scope type_scope.

Class Decidable (P : Prop) := dec : {P} + {~P}.

Notation DecidableRel R := (forall x y, Decidable (R x y)).

Ltac destruct_decidable_step :=
  match goal with
  | [ H : Decidable _ |- _ ] => destruct H
  end.
Ltac destruct_decidable := repeat destruct_decidable_step.

Local Ltac pre_decide :=
  repeat (intros
          || destruct_decidable
          || subst
          || split
          || unfold Decidable in *
          || hnf ).

Local Ltac solve_decidable_transparent_with tac :=
  pre_decide;
  try solve [ left; abstract tac
            | right; abstract tac
            | decide equality; eauto with nocore ].

Local Ltac solve_decidable_transparent := solve_decidable_transparent_with firstorder.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.

Global Instance dec_True : Decidable True := left I.
Global Instance dec_False : Decidable False := right (fun x => x).
Global Instance dec_or {A B} `{Decidable A, Decidable B} : Decidable (A \/ B) := _.
Global Instance dec_and {A B} `{Decidable A, Decidable B} : Decidable (A /\ B) := _.
Global Instance dec_impl {A B} `{Decidable (B \/ ~A)} : Decidable (A -> B) | 3 := _.
Global Instance dec_impl_simple {A B} `{Decidable A, Decidable B} : Decidable (A -> B) := _.
Global Instance dec_iff {A B} `{Decidable A, Decidable B} : Decidable (A <-> B) := _.
Lemma dec_not {A} `{Decidable A} : Decidable (~A).
Proof. solve_decidable_transparent. Defined.
(** Disallow infinite loops of dec_not *)
Hint Extern 0 (Decidable (~?A)) => apply (@dec_not A) : typeclass_instances.

Global Instance dec_eq_unit : DecidableRel (@eq unit) := _.
Global Instance dec_eq_bool : DecidableRel (@eq bool) := _.
Global Instance dec_eq_Empty_set : DecidableRel (@eq Empty_set) := _.
Global Instance dec_eq_nat : DecidableRel (@eq nat) := _.
Global Instance dec_eq_prod {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A * B)) := _.
Global Instance dec_eq_sum {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A + B)) := _.

Lemma Decidable_respects_iff A B (H : A <-> B) : (Decidable A -> Decidable B) * (Decidable B -> Decidable A).
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_impl A B (H : A <-> B) : Decidable A -> Decidable B.
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_flip_impl A B (H : A <-> B) : Decidable B -> Decidable A.
Proof. solve_decidable_transparent. Defined.
