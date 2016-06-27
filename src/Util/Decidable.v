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

Ltac pre_decide :=
  repeat (intros
          || destruct_decidable
          || subst
          || split
          || unfold Decidable in *
          || hnf ).

Ltac solve_decidable_transparent_with tac :=
  pre_decide;
  try solve [ left; abstract tac
            | right; abstract tac
            | decide equality; eauto with nocore ].

Ltac solve_decidable_transparent := solve_decidable_transparent_with firstorder.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.

Global Instance dec_True : Decidable True | 10 := left I.
Global Instance dec_False : Decidable False | 10 := right (fun x => x).
Global Instance dec_or {A B} `{Decidable A, Decidable B} : Decidable (A \/ B) | 10. exact _. Defined.
Global Instance dec_and {A B} `{Decidable A, Decidable B} : Decidable (A /\ B) | 10. exact _. Defined.
Global Instance dec_impl {A B} `{Decidable (B \/ ~A)} : Decidable (A -> B) | 10. exact _. Defined.
Global Instance dec_impl_simple {A B} `{Decidable A, Decidable B} : Decidable (A -> B) | 10. exact _. Defined.
Global Instance dec_iff {A B} `{Decidable A, Decidable B} : Decidable (A <-> B) | 10. exact _. Defined.
Lemma dec_not {A} `{Decidable A} : Decidable (~A).
Proof. solve_decidable_transparent. Defined.
(** Disallow infinite loops of dec_not *)
Hint Extern 0 (Decidable (~?A)) => apply (@dec_not A) : typeclass_instances.

Global Instance dec_eq_unit : DecidableRel (@eq unit) | 10. exact _. Defined.
Global Instance dec_eq_bool : DecidableRel (@eq bool) | 10. exact _. Defined.
Global Instance dec_eq_Empty_set : DecidableRel (@eq Empty_set) | 10. exact _. Defined.
Global Instance dec_eq_nat : DecidableRel (@eq nat) | 10. exact _. Defined.
Global Instance dec_eq_prod {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A * B)) | 10. exact _. Defined.
Global Instance dec_eq_sum {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A + B)) | 10. exact _. Defined.

Lemma Decidable_respects_iff A B (H : A <-> B) : (Decidable A -> Decidable B) * (Decidable B -> Decidable A).
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_impl A B (H : A <-> B) : Decidable A -> Decidable B.
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_flip_impl A B (H : A <-> B) : Decidable B -> Decidable A.
Proof. solve_decidable_transparent. Defined.

(** For dubious compatibility with [eauto using]. *)
Hint Extern 2 (Decidable _) => progress unfold Decidable : typeclass_instances core.
