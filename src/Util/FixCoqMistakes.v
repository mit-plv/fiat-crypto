(** * Fixes *)
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
