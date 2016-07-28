(** Typeclass for decidable propositions *)

Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Equality.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.

Local Open Scope type_scope.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.

Notation DecidableRel R := (forall x y, Decidable (R x y)).

Global Instance hprop_eq_dec {A} `{DecidableRel (@eq A)} : IsHPropRel (@eq A) | 10.
Proof. repeat intro; apply UIP_dec; trivial with nocore. Qed.

Global Instance eq_dec_hprop {A} {x y : A} `{hp : IsHProp A} : Decidable (@eq A x y) | 5.
Proof. left; apply hp. Qed.

Ltac no_equalities_about x0 y0 :=
  lazymatch goal with
  | [ H' : x0 = y0 |- _ ] => fail
  | [ H' : y0 = x0 |- _ ] => fail
  | [ H' : x0 <> y0 |- _ ] => fail
  | [ H' : y0 <> x0 |- _ ] => fail
  | _ => idtac
  end.

Ltac destruct_decidable_step :=
  match goal with
  | [ H : Decidable _ |- _ ] => destruct H
  | [ H : forall x y : ?A, Decidable (x = y), x0 : ?A, y0 : ?A  |- _ ]
    => no_equalities_about x0 y0; destruct (H x0 y0)
  | [ H : forall a0 (x y : _), Decidable (x = y), x0 : ?A, y0 : ?A  |- _ ]
    => no_equalities_about x0 y0; destruct (H _ x0 y0)
  end.
Ltac destruct_decidable := repeat destruct_decidable_step.

Ltac pre_decide_destruct_sigma_step :=
  match goal with
  | [ H : sigT _ |- _ ] => destruct H
  | [ H : sig _ |- _ ] => destruct H
  | [ H : ex _ |- _ ] => destruct H
  end.
Ltac pre_decide_destruct_sigma := repeat pre_decide_destruct_sigma_step.

Ltac pre_decide :=
  repeat (intros
          || destruct_decidable
          || split
          || pre_decide_destruct_sigma
          || unfold Decidable in *
          || hnf).

(** Put the [subst] and reasoning about equalities after the [left]
    and [right]; opaque equality proofs should not block decidability
    proofs. *)
Ltac post_decide :=
  repeat (intros
          || subst
          || pre_hprop).

Ltac solve_decidable_transparent_with tac :=
  pre_decide;
  try solve [ left; abstract (post_decide; tac)
            | right; abstract (post_decide; tac)
            | decide equality; eauto with nocore ].

Ltac solve_decidable_transparent := solve_decidable_transparent_with firstorder.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.
Local Hint Extern 1 => progress inversion_sigma : core.

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
Global Instance dec_eq_prod {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A * B)) | 10. exact _. Defined.
Global Instance dec_eq_sum {A B} `{DecidableRel (@eq A), DecidableRel (@eq B)} : DecidableRel (@eq (A + B)) | 10. exact _. Defined.
Global Instance dec_eq_sigT_hprop {A P} `{DecidableRel (@eq A), forall a : A, IsHProp (P a)} : DecidableRel (@eq (@sigT A P)) | 10. exact _. Defined.
Global Instance dec_eq_sig_hprop {A} {P : A -> Prop} `{DecidableRel (@eq A), forall a : A, IsHProp (P a)} : DecidableRel (@eq (@sig A P)) | 10. exact _. Defined.
Global Instance dec_eq_nat : DecidableRel (@eq nat) | 10. exact _. Defined.
Global Instance dec_eq_N : DecidableRel (@eq N) | 10 := N.eq_dec.
Global Instance dec_eq_Z : DecidableRel (@eq Z) | 10 := Z.eq_dec.

Lemma Decidable_respects_iff A B (H : A <-> B) : (Decidable A -> Decidable B) * (Decidable B -> Decidable A).
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_impl A B (H : A <-> B) : Decidable A -> Decidable B.
Proof. solve_decidable_transparent. Defined.

Lemma Decidable_iff_to_flip_impl A B (H : A <-> B) : Decidable B -> Decidable A.
Proof. solve_decidable_transparent. Defined.

Lemma dec_bool : forall {P} {Pdec:Decidable P}, (if dec P then true else false) = true -> P.
Proof. intros. destruct dec; solve [ auto | discriminate ]. Qed.

Ltac vm_decide := apply dec_bool; vm_compute; reflexivity.
Ltac lazy_decide := apply dec_bool; lazy; reflexivity.

Ltac vm_decide_no_check := apply dec_bool; vm_cast_no_check (eq_refl true).
Ltac lazy_decide_no_check := apply dec_bool; exact_no_check (eq_refl true).

(** For dubious compatibility with [eauto using]. *)
Hint Extern 2 (Decidable _) => progress unfold Decidable : typeclass_instances core.
