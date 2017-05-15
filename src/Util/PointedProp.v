(** * Propositions with a distinguished point representing true *)
(** This allows for something between [bool] and [Prop], where we can
    computationally reduce things like [True /\ True], but can still
    express equality of types. *)
Require Import Coq.Setoids.Setoid.
Require Import Crypto.Util.Notations.

Delimit Scope pointed_prop_scope with pointed_prop.
Delimit Scope option_pointed_prop_scope with option_pointed_prop.
Inductive pointed_Prop := trivial | inject (_ : Prop).
Bind Scope pointed_prop_scope with pointed_Prop.

Definition to_prop (x : pointed_Prop) : Prop
  := match x with
     | trivial => True
     | inject p => p
     end.

Coercion option_pointed_Prop_of_bool (x : bool) : option pointed_Prop
  := if x then Some trivial else None.
Coercion option_pointed_Prop_of_pointed_Prop (x : pointed_Prop) : option pointed_Prop
  := Some x.

Definition prop_of_option (x : option pointed_Prop) : Prop
  := match x with
     | Some p => to_prop p
     | None => False
     end.

Definition and_pointed_Prop (x y : pointed_Prop) : pointed_Prop
  := match x, y with
     | trivial, y => y
     | x, trivial => x
     | inject p, inject q => inject (p /\ q)
     end.

Definition or_pointed_Prop (x y : pointed_Prop) : pointed_Prop
  := match x, y with
     | trivial, _ => trivial
     | _, trivial => trivial
     | inject p, inject q => inject (p \/ q)
     end.

Definition impl_pointed_Prop (x y : pointed_Prop) : pointed_Prop
  := match x, y with
     | trivial, y => y
     | _, trivial => trivial
     | inject p, inject q => inject (p -> q)
     end.

Definition not_option_pointed_Prop (x : option pointed_Prop) : option pointed_Prop
  := match x with
     | Some trivial => None
     | None => Some trivial
     | Some (inject p) => Some (inject (~p))
     end.
Arguments not_option_pointed_Prop _%option_pointed_prop.

Definition and_option_pointed_Prop (x y : option pointed_Prop) : option pointed_Prop
  := match x, y with
     | Some x, Some y => Some (and_pointed_Prop x y)
     | _, _ => None
     end.
Arguments and_option_pointed_Prop (_ _)%option_pointed_prop.

Definition or_option_pointed_Prop (x y : option pointed_Prop) : option pointed_Prop
  := match x, y with
     | Some x, Some y => Some (or_pointed_Prop x y)
     | Some x, None => Some x
     | None, Some y => Some y
     | None, None => None
     end.
Arguments or_option_pointed_Prop (_ _)%option_pointed_prop.

Definition impl_option_pointed_Prop (x y : option pointed_Prop) : option pointed_Prop
  := match x, y with
     | None, _ => Some trivial
     | Some x, Some y => Some (impl_pointed_Prop x y)
     | Some p, None => not_option_pointed_Prop p
     end.
Arguments impl_option_pointed_Prop (_ _)%option_pointed_prop.

Infix "/\" := and_pointed_Prop : pointed_prop_scope.
Infix "\/" := or_pointed_Prop : pointed_prop_scope.
Infix "->" := impl_pointed_Prop : pointed_prop_scope.
Infix "/\" := and_option_pointed_Prop : option_pointed_prop_scope.
Infix "\/" := or_option_pointed_Prop : option_pointed_prop_scope.
Infix "->" := impl_option_pointed_Prop : option_pointed_prop_scope.
Notation "~ P" := (not_option_pointed_Prop P) : option_pointed_prop_scope.

Ltac inversion_pointed_Prop_step :=
  match goal with
  | [ H : inject _ = inject _ |- _ ] => progress (inversion H; clear H)
  end.
Ltac inversion_pointed_Prop := repeat inversion_pointed_Prop_step.

Create HintDb push_prop_of_option discriminated.
Create HintDb push_to_prop discriminated.
Create HintDb push_eq_trivial discriminated.
Create HintDb push_eq_Some_trivial discriminated.
Hint Extern 1 => progress autorewrite with push_prop_of_option in * : push_prop_of_option.
Hint Extern 1 => progress autorewrite with push_to_prop in * : push_to_prop.
Hint Extern 1 => progress autorewrite with push_eq_trivial in * : push_eq_trivial.
Hint Extern 1 => progress autorewrite with push_eq_Some_trivial in * : push_eq_Some_trivial.

Lemma to_prop_and P Q : to_prop (P /\ Q)%pointed_prop
                        <-> (to_prop P /\ to_prop Q).
Proof. destruct P, Q; simpl; tauto. Qed.
Hint Rewrite to_prop_and : push_to_prop.

Lemma to_prop_or P Q : to_prop (P \/ Q)%pointed_prop
                       <-> (to_prop P \/ to_prop Q).
Proof. destruct P, Q; simpl; tauto. Qed.
Hint Rewrite to_prop_or : push_to_prop.

Lemma to_prop_impl P Q : to_prop (impl_pointed_Prop P Q)%pointed_prop
                         <-> (to_prop P -> to_prop Q).
Proof. destruct P, Q; simpl; tauto. Qed.
Hint Rewrite to_prop_impl : push_to_prop.

Lemma prop_of_option_and P Q : prop_of_option (P /\ Q)%option_pointed_prop
                               <-> (prop_of_option P /\ prop_of_option Q).
Proof. destruct P, Q; simpl; autorewrite with push_to_prop; tauto. Qed.
Hint Rewrite prop_of_option_and : push_prop_of_option.

Lemma prop_of_option_or P Q : prop_of_option (P \/ Q)%option_pointed_prop
                               <-> (prop_of_option P \/ prop_of_option Q).
Proof. destruct P, Q; simpl; autorewrite with push_to_prop; tauto. Qed.
Hint Rewrite prop_of_option_or : push_prop_of_option.

Lemma prop_of_option_impl P Q : prop_of_option (impl_option_pointed_Prop P Q)%option_pointed_prop
                               <-> (prop_of_option P -> prop_of_option Q).
Proof. destruct P as [ [|P] |], Q as [ [|Q] |]; simpl; tauto. Qed.
Hint Rewrite prop_of_option_impl : push_prop_of_option.

Lemma prop_of_option_not P : prop_of_option (~P)%option_pointed_prop
                               <-> (~prop_of_option P).
Proof. destruct P as [ [|] | ]; simpl; tauto. Qed.
Hint Rewrite prop_of_option_not : push_prop_of_option.

Lemma eq_trivial_and P Q : (P /\ Q)%pointed_prop = trivial
                           <-> (P = trivial /\ Q = trivial).
Proof. destruct P, Q; simpl; intuition congruence. Qed.
Hint Rewrite eq_trivial_and : push_eq_trivial.

Lemma eq_trivial_or P Q : (P \/ Q)%pointed_prop = trivial
                          <-> (P = trivial \/ Q = trivial).
Proof. destruct P, Q; simpl; intuition congruence. Qed.
Hint Rewrite eq_trivial_or : push_eq_trivial.

Lemma eq_trivial_impl P Q : (impl_pointed_Prop P Q)%pointed_prop = trivial
                         <-> Q = trivial.
Proof. destruct P, Q; simpl; intuition congruence. Qed.
Hint Rewrite eq_trivial_impl : push_eq_trivial.

Lemma eq_Some_trivial_and P Q : (P /\ Q)%option_pointed_prop = Some trivial
                               <-> (P = Some trivial /\ Q = Some trivial).
Proof. destruct P as [ []|], Q as [ []|]; simpl; intuition congruence. Qed.
Hint Rewrite eq_Some_trivial_and : push_eq_Some_trivial.

Lemma eq_Some_trivial_or P Q : (P \/ Q)%option_pointed_prop = Some trivial
                               <-> (P = Some trivial \/ Q = Some trivial).
Proof. destruct P as [ []|], Q as [ []|]; simpl; intuition congruence. Qed.
Hint Rewrite eq_Some_trivial_or : push_eq_Some_trivial.

Lemma eq_Some_trivial_impl P Q : (impl_option_pointed_Prop P Q)%option_pointed_prop = Some trivial
                               <-> (P = None \/ Q = Some trivial).
Proof. destruct P as [ [|P] |], Q as [ [|Q] |]; simpl; intuition congruence. Qed.
Hint Rewrite eq_Some_trivial_impl : push_eq_Some_trivial.

Lemma eq_Some_trivial_not P : (~P)%option_pointed_prop = Some trivial
                               <-> P = None.
Proof. destruct P as [ [|] | ]; simpl; intuition congruence. Qed.
Hint Rewrite eq_Some_trivial_not : push_eq_Some_trivial.
