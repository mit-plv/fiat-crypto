Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Notations.

Definition compose {A B} {C : B -> Type} (g : forall b : B, C b) (f : A -> B) (x : A)
  := g (f x).
Global Arguments compose {A B C} g f x / .

Infix "'o'" := compose : function_scope.
Infix "∘" := compose : function_scope.

Typeclasses Opaque compose.

Global Instance Proper_compose {A B C}
      {RA RB RC}
  : Proper ((RB ==> RC) ==> (RA ==> RB) ==> RA ==> RC) (@compose A B (fun _ => C)).
Proof. cbv in *; eauto. Qed.

Global Instance Proper_compose_app {A B C} (g : B -> C) (f : A -> B)
      {RA RB RC}
      {Hg : Proper (RB ==> RC) g}
      {Hf : Proper (RA ==> RB) f}
  : Proper (RA ==> RC) (g ∘ f).
Proof. cbv in *; eauto. Qed.

Ltac Proper_compose_hint :=
  lazymatch goal with
  | [ |- Proper _ (fun x => ?g (?f x)) ]
    => simple eapply (@Proper_compose_app _ _ _ g f)
  end.

(*Global Hint Extern 2 (Proper _ (fun x => ?g (?f x))) => simple eapply (@Proper_compose_app _ _ _ g f) : typeclass_instances.*)
