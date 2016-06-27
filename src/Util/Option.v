Require Import Coq.Classes.Morphisms.

Global Instance option_rect_Proper_nd {A T}
  : Proper ((pointwise_relation _ eq) ==> eq  ==> eq ==> eq) (@option_rect A (fun _ => T)).
Proof.
  intros ?? H ??? [|]??; subst; simpl; congruence.
Qed.

Global Instance option_rect_Proper_nd' {A T}
  : Proper ((pointwise_relation _ eq) ==> eq  ==> forall_relation (fun _ => eq)) (@option_rect A (fun _ => T)).
Proof.
  intros ?? H ??? [|]; subst; simpl; congruence.
Qed.

Hint Extern 1 (Proper _ (@option_rect ?A (fun _ => ?T))) => exact (@option_rect_Proper_nd' A T) : typeclass_instances.

Lemma option_rect_option_map : forall {A B C} (f:A->B) some none v,
    option_rect (fun _ => C) (fun x => some (f x)) none v = option_rect (fun _ => C) some none (option_map f v).
Proof.
  destruct v; reflexivity.
Qed.

Lemma option_rect_function {A B C S' N' v} f
  : f (option_rect (fun _ : option A => option B) S' N' v)
    = option_rect (fun _ : option A => C) (fun x => f (S' x)) (f N') v.
Proof. destruct v; reflexivity. Qed.

(*
Ltac commute_option_rect_Let_In := (* pull let binders out side of option_rect pattern matching *)
  idtac;
  lazymatch goal with
  | [ |- ?LHS = option_rect ?P ?S ?N (Let_In ?x ?f) ]
    => (* we want to just do a [change] here, but unification is stupid, so we have to tell it what to unfold in what order *)
    cut (LHS = Let_In x (fun y => option_rect P S N (f y))); cbv beta;
    [ set_evars;
      let H := fresh in
      intro H;
      rewrite H;
      clear;
      abstract (cbv [Let_In]; reflexivity)
    | ]
  end.
*)

(** TODO: possibly move me, remove local *)
Ltac replace_option_match_with_option_rect :=
  idtac;
  lazymatch goal with
  | [ |- _ = ?RHS :> ?T ]
    => lazymatch RHS with
       | match ?a with None => ?N | Some x => @?S x end
         => replace RHS with (option_rect (fun _ => T) S N a) by (destruct a; reflexivity)
       end
  end.

Ltac simpl_option_rect := (* deal with [option_rect _ _ _ None] and [option_rect _ _ _ (Some _)] *)
  repeat match goal with
         | [ |- context[option_rect ?P ?S ?N None] ]
           => change (option_rect P S N None) with N
         | [ |- context[option_rect ?P ?S ?N (Some ?x) ] ]
           => change (option_rect P S N (Some x)) with (S x); cbv beta
         end.
