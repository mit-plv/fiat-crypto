(** * Propositions with a distinguished point representing true *)
(** This allows for something between [bool] and [Prop], where we can
    computationally reduce things like [True /\ True], but can still
    express equality of types. *)
Require Import Crypto.Util.Notations.

Delimit Scope pointed_prop_scope with pointed_prop.
Inductive pointed_Prop := trivial | inject (_ : Prop).
Bind Scope pointed_prop_scope with pointed_Prop.

Definition to_prop (x : pointed_Prop) : Prop
  := match x with
     | trivial => True
     | inject p => p
     end.

Coercion option_pointed_Prop_of_bool (x : bool) : option pointed_Prop
  := if x then Some trivial else None.

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

Infix "/\" := and_pointed_Prop : pointed_prop_scope.
Infix "\/" := or_pointed_Prop : pointed_prop_scope.
Infix "->" := impl_pointed_Prop : pointed_prop_scope.

Ltac inversion_pointed_Prop_step :=
  match goal with
  | [ H : inject _ = inject _ |- _ ] => progress (inversion H; clear H)
  end.
Ltac inversion_pointed_Prop := repeat inversion_pointed_Prop_step.
