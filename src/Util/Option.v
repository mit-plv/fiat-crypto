Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Definition bind {A B} (v : option A) (f : A -> option B) : option B
  := match v with
     | Some v => f v
     | None => None
     end.

Module Export Notations.
  Delimit Scope option_scope with option.
  Bind Scope option_scope with option.

  Notation "A <- X ; B" := (bind X (fun A => B%option)) : option_scope.
End Notations.

Section Relations.
  Definition option_eq {A} eq (x y : option A) :=
    match x with
    | None    => y = None
    | Some ax => match y with
                 | None => False
                 | Some ay => eq ax ay
                 end
    end.

  Local Ltac t :=
    cbv; repeat (break_match || intro || intuition congruence ||
                 solve [ apply reflexivity
                       | apply symmetry; eassumption
                       | eapply transitivity; eassumption ] ).

  Global Instance Reflexive_option_eq {T} {R} {Reflexive_R:@Reflexive T R}
    : Reflexive (option_eq R). Proof. t. Qed.

  Global Instance Transitive_option_eq {T} {R} {Transitive_R:@Transitive T R}
    : Transitive (option_eq R). Proof. t. Qed.

  Global Instance Symmetric_option_eq {T} {R} {Symmetric_R:@Symmetric T R}
    : Symmetric (option_eq R). Proof. t. Qed.

  Global Instance Equivalence_option_eq {T} {R} {Equivalence_R:@Equivalence T R}
    : Equivalence (option_eq R). Proof. split; exact _. Qed.
End Relations.

Global Instance Proper_option_rect_nd_changebody
      {A B:Type} {RB:relation B} {a:option A}
  : Proper (pointwise_relation _ RB ==> RB ==> RB) (fun S N => option_rect (fun _ => B) S N a).
Proof. cbv; repeat (intro || break_match); intuition. Qed.

(* FIXME: there used to be a typeclass resolution hint here, something like
  Hint Extern 1 (Proper _ (@option_rect ?A (fun _ => ?B))) => exact (@Proper_option_rect_nd_changebody A B _ _) : typeclass_instances.
 but I could not get it working after generalizing [RB] from [Logic.eq] ~ andreser *)

Global Instance Proper_option_rect_nd_changevalue
      {A B RA RB} some {Proper_some: Proper (RA==>RB) some}
  : Proper (RB ==> option_eq RA ==> RB) (@option_rect A (fun _ => B) some).
Proof. cbv; repeat (intro || break_match || f_equiv || intuition congruence). Qed.

Lemma option_rect_false_returns_true_iff
      {T} {R} {reflexiveR:Reflexive R}
      (f:T->bool) {Proper_f:Proper(R==>eq)f} (o:option T) :
  option_rect (fun _ => bool) f false o = true <-> exists s:T, option_eq R o (Some s) /\ f s = true.
Proof.
  unfold option_rect; break_match; repeat intuition (destruct_head ex; eauto); [ | | congruence.. ].
  { repeat esplit; simpl; easy. }
  { match goal with [H : f _ = true |- f _ = true ] =>
                    solve [rewrite <- H; eauto] end. }
Qed.

Lemma option_rect_false_returns_true_iff_eq
      {T} (f:T->bool) (o:option T) :
  option_rect (fun _ => bool) f false o = true <-> exists s:T, Logic.eq o (Some s) /\ f s = true.
Proof. unfold option_rect; break_match; repeat intuition (destruct_head ex; eauto); congruence. Qed.

Lemma option_rect_option_map : forall {A B C} (f:A->B) some none v,
    option_rect (fun _ => C) (fun x => some (f x)) none v = option_rect (fun _ => C) some none (option_map f v).
Proof.
  destruct v; reflexivity.
Qed.

Lemma option_map_map : forall {A B C} (f:A->B) (g:B->C) v,
    option_map g (option_map f v) = option_map (fun v => g (f v)) v.
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

Definition option_leq_to_eq {A} (x y : option A) : x = y -> option_eq eq x y.
Proof. destruct x; intro; subst; simpl; reflexivity. Defined.

Definition option_eq_to_leq {A} (x y : option A) : option_eq eq x y -> x = y.
Proof.
  destruct x, y; simpl;
    try solve [ intros []
              | apply f_equal
              | reflexivity
              | apply eq_sym ].
Defined.

Lemma option_leq_to_eq_to_leq {A x y} v : @option_eq_to_leq A x y (@option_leq_to_eq A x y v) = v.
Proof.
  destruct x; subst; simpl; reflexivity.
Qed.

Lemma option_eq_to_leq_to_eq {A x y} v : @option_leq_to_eq A x y (@option_eq_to_leq A x y v) = v.
Proof.
  compute in *.
  repeat first [ progress subst
               | progress break_innermost_match_step
               | reflexivity ].
Qed.

Lemma UIP_None {A} (p q : @None A = @None A) : p = q.
Proof.
  rewrite <- (option_leq_to_eq_to_leq p), <- (option_leq_to_eq_to_leq q); simpl; reflexivity.
Qed.

Definition invert_Some {A} (x : option A) : match x with
                                            | Some _ => A
                                            | None => unit
                                            end
  := match x with
     | Some x' => x'
     | None => tt
     end.

Lemma invert_eq_Some {A x y} (p : Some x = Some y) : { pf : x = y | @option_eq_to_leq A (Some x) (Some y) pf = p }.
Proof.
  refine (exist _ _ (option_leq_to_eq_to_leq _)).
Qed.

Ltac inversion_option_step :=
  match goal with
  | [ H : Some _ = Some _ |- _ ] => apply option_leq_to_eq in H; unfold option_eq in H
  | [ H : Some _ = Some _ |- _ ]
    => let H' := fresh in
       rename H into H';
       destruct (invert_eq_Some H') as [H ?]; subst H'
  | [ H : None = Some _ |- _ ] => solve [ inversion H ]
  | [ H : Some _ = None |- _ ] => solve [ inversion H ]
  | [ H : None = None |- _ ] => clear H
  | [ H : None = None |- _ ]
    => assert (eq_refl = H) by apply UIP_None; subst H
  end.

Ltac inversion_option := repeat inversion_option_step.
