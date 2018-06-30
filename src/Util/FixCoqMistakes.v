(** * Fixes *)
Require Import Coq.Classes.Morphisms.
Require Export Crypto.Util.GlobalSettings.

(** Coq is poorly designed in some ways.  We fix some of these issues
    in this file. *)

(** [intuition] means [intuition auto with *].  This is very wrong and
    fragile and slow.  We make [intuition] mean [intuition auto]. *)
Tactic Notation "intuition" tactic3(tactic) := intuition tactic.
Tactic Notation "intuition" := intuition auto.

(** [firstorder] means [firstorder auto with *].  This is very wrong
    and fragile and slow.  We make [firstorder] mean [firstorder
    auto]. *)
Global Set Firstorder Solver auto.

(** A version of [intuition] that allows you to see how the old
    [intuition] tactic solves the proof. *)
Ltac debug_intuition := idtac "<infomsg>Warning: debug_intuition should not be used in production code.</infomsg>"; intuition debug auto with *.

(** [Coq.Init.Logic.f_equal2] is opaque.  A transparent version would serve us better. *)
Definition f_equal2 {A1 A2 B} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2} (H : x1 = y1)
  := match H in (_ = y) return (x2 = y2 -> f x1 x2 = f y y2) with
     | eq_refl =>
       fun H0 : x2 = y2 =>
         match H0 in (_ = y) return (f x1 x2 = f x1 y) with
         | eq_refl => eq_refl
         end
     end.

(** Work around BZ#5341, https://coq.inria.fr/bugs/show_bug.cgi?id=5341, [subst] fails with bogus error message about universe polymorphism *)
Local Theorem create_internal_eq_rew_r_dep :  forall A (a : A) (x : A) (e : a = x),
    e = e -> True.
Proof.
  intros ? ? ? H.
  match goal with |- ?G => assert G end;
    [ rewrite -> H
    | rewrite <- H ];
    constructor.
Defined.

(** Typeclass resolution is stupid.  So we write a tactic that makes
    it less stupid.  We may occasionally have to redeclare the
    instance, because, unfortunately, instance priorities cannot be
    negative (which is also stupid). *)
(* We don't actually have function extensionality
Ltac make_rel do_pointwise T :=
  lazymatch T with
  | (?A -> ?B)
    => let RA := make_rel true A in
      let RB := make_rel do_pointwise B in
      let default _ := constr:(@respectful A B RA RB) in
      lazymatch do_pointwise with
      | true => lazymatch RA with
               | eq => constr:(@pointwise_relation A B RB)
               | _ => default ()
               end
      | _ => default ()
      end
  | (forall a : ?A, ?B)
    => let B' := fresh in
      constr:(@forall_relation A (fun a : A => B) (fun a : A => match B with B' => ltac:(let B'' := (eval cbv delta [B'] in B') in
                                                                                  let RB := make_rel do_pointwise B in
                                                                                  exact RB) end))
  | _ => constr:(@eq T)
  end.
*)
Ltac make_eq_rel T :=
  lazymatch T with
  | (?A -> ?B)
    => let RB := make_eq_rel B in
      constr:(@respectful A B (@eq A) RB)
  | (forall a : ?A, ?B)
    => let B' := fresh in
      constr:(@forall_relation A (fun a : A => B) (fun a : A => match B with B' => ltac:(let B'' := (eval cbv delta [B'] in B') in
                                                                                  let RB := make_eq_rel B in
                                                                                  exact RB) end))
  | _ => constr:(@eq T)
  end.
Ltac solve_Proper_eq :=
  match goal with
  | [ |- @Proper ?A ?R ?f ]
    => let R' := make_eq_rel A in
      unify R R';
      apply (@reflexive_proper A R')
  end.
Hint Extern 0 (Proper _ _) => solve_Proper_eq : typeclass_instances.
