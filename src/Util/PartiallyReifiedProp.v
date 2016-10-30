(** * Propositions with a distinguished representation of [True], [False], [and], [or], and [impl] *)
(** This allows for something between [bool] and [Prop], where we can
    computationally reduce things like [True /\ True], but can still
    express equality of types. *)
Require Import Coq.Setoids.Setoid.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.

Delimit Scope reified_prop_scope with reified_prop.
Inductive reified_Prop := rTrue | rFalse | rAnd (x y : reified_Prop) | rOr (x y : reified_Prop) | rImpl (x y : reified_Prop) | rForall {T} (f : T -> reified_Prop) | rEq {T} (x y : T) | rEqRefl {T} (x : T) | inject (_ : Prop).
Bind Scope reified_prop_scope with reified_Prop.

Fixpoint to_prop (x : reified_Prop) : Prop
  := match x with
     | rTrue => True
     | rFalse => False
     | rAnd x y => to_prop x /\ to_prop y
     | rOr x y => to_prop x \/ to_prop y
     | rImpl x y => to_prop x -> to_prop y
     | @rForall _ f => forall x, to_prop (f x)
     | @rEq _ x y => x = y
     | @rEqRefl _ x => x = x
     | inject x => x
     end.

Coercion reified_Prop_of_bool (x : bool) : reified_Prop
  := if x then rTrue else rFalse.

Definition and_reified_Prop (x y : reified_Prop) : reified_Prop
  := match x, y with
     | rTrue, y => y
     | x, rTrue => x
     | rFalse, y => rFalse
     | x, rFalse => rFalse
     | rEq T a b, rEq T' a' b' => rEq (a, a') (b, b')
     | x', y' => rAnd x' y'
     end.
Definition or_reified_Prop (x y : reified_Prop) : reified_Prop
  := match x, y with
     | rTrue, y => rTrue
     | x, rTrue => rTrue
     | rFalse, y => y
     | x, rFalse => x
     | x', y' => rOr x' y'
     end.
Definition impl_reified_Prop (x y : reified_Prop) : reified_Prop
  := match x, y with
     | rTrue, y => y
     | x, rTrue => rTrue
     | rFalse, y => rTrue
     | rImpl x rFalse, rFalse => x
     | x', y' => rImpl x' y'
     end.

Infix "/\" := and_reified_Prop : reified_prop_scope.
Infix "\/" := or_reified_Prop : reified_prop_scope.
Infix "->" := impl_reified_Prop : reified_prop_scope.
Infix "=" := rEq : reified_prop_scope.
Notation "~ P" := (P -> rFalse)%reified_prop : reified_prop_scope.
Notation "∀  x .. y , P" := (rForall (fun x => .. (rForall (fun y => P%reified_prop)) .. ))
                              (at level 200, x binder, y binder, right associativity) : reified_prop_scope.

Definition reified_Prop_eq (x y : reified_Prop)
  := match x, y with
     | rTrue, _ => y = rTrue
     | rFalse, _ => y = rFalse
     | rAnd x0 x1, rAnd y0 y1
       => x0 = y0 /\ x1 = y1
     | rAnd _ _, _ => False
     | rOr x0 x1, rOr y0 y1
       => x0 = y0 /\ x1 = y1
     | rOr _ _, _ => False
     | rImpl x0 x1, rImpl y0 y1
       => x0 = y0 /\ x1 = y1
     | rImpl _ _, _ => False
     | @rForall Tx fx, @rForall Ty fy
       => exists pf : Tx = Ty,
                      forall x, fx x = fy (eq_rect _ (fun t => t) x _ pf)
     | rForall _ _, _ => False
     | @rEq Tx x0 x1, @rEq Ty y0 y1
       => exists pf : Tx = Ty,
                      eq_rect _ (fun t => t) x0 _ pf = y0
                      /\ eq_rect _ (fun t => t) x1 _ pf = y1
     | rEq _ _ _, _ => False
     | @rEqRefl Tx x, @rEqRefl Ty y
       => exists pf : Tx = Ty,
                      eq_rect _ (fun t => t) x _ pf = y
     | rEqRefl _ _, _ => False
     | inject x, inject y => x = y
     | inject _, _ => False
     end.

Section rel.
  Local Ltac t :=
    cbv;
    repeat (break_match
            || intro
            || (simpl in * )
            || intuition try congruence
            || (exists eq_refl)
            || eauto
            || subst
            || apply conj
            || destruct_head' ex
            || solve [ apply reflexivity
                     | apply symmetry; eassumption
                     | eapply transitivity; eassumption ] ).

  Global Instance Reflexive_reified_Prop_eq : Reflexive reified_Prop_eq.
  Proof. t. Qed.
  Global Instance Symmetric_reified_Prop_eq : Symmetric reified_Prop_eq.
  Proof. t. Qed.
  Global Instance Transitive_reified_Prop_eq : Transitive reified_Prop_eq.
  Proof. t. Qed.
  Global Instance Equivalence_reified_Prop_eq : Equivalence reified_Prop_eq.
  Proof. split; exact _. Qed.
End rel.

Definition reified_Prop_leq_to_eq (x y : reified_Prop) : x = y -> reified_Prop_eq x y.
Proof. intro; subst; simpl; reflexivity. Qed.

Ltac inversion_reified_Prop_step :=
  let do_on H := apply reified_Prop_leq_to_eq in H; unfold reified_Prop_eq in H in
  match goal with
  | [ H : False |- _ ] => solve [ destruct H ]
  | [ H : (_ = _ :> reified_Prop) /\ (_ = _ :> reified_Prop) |- _ ] => destruct H
  | [ H : ?x = ?x :> reified_Prop |- _ ] => clear H
  | [ H : exists pf : _ = _ :> Type, forall x, _ = _ :> reified_Prop |- _ ]
    => destruct H as [? H]; subst; simpl @eq_rect in H
  | [ H : ?x = _ :> reified_Prop |- _ ] => is_var x; subst x
  | [ H : _ = ?y :> reified_Prop |- _ ] => is_var y; subst y
  | [ H : rTrue = rFalse |- _ ] => solve [ inversion H ]
  | [ H : rFalse = rTrue |- _ ] => solve [ inversion H ]
  | [ H : rTrue = _ |- _ ] => do_on H; progress subst
  | [ H : rFalse = _ |- _ ] => do_on H; progress subst
  | [ H : rAnd _ _ = _ |- _ ] => do_on H
  | [ H : rOr _ _ = _ |- _ ] => do_on H
  | [ H : rImpl _ _ = _ |- _ ] => do_on H
  | [ H : rForall _ = _ |- _ ] => do_on H
  | [ H : rEq _ _ = _ |- _ ] => do_on H
  | [ H : rEqRefl _ = _ |- _ ] => do_on H
  | [ H : inject _ = _ |- _ ] => do_on H
  end.
Ltac inversion_reified_Prop := repeat inversion_reified_Prop_step.

Lemma to_prop_and_reified_Prop x y : to_prop (x /\ y) <-> (to_prop x /\ to_prop y).
Proof.
  destruct x, y; simpl; try tauto.
  { split; intro H; inversion H; subst; repeat split. }
Qed.
