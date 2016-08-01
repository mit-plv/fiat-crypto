(** * Fixes *)
Require Export Crypto.Util.GlobalSettings.

(** Coq is poorly designed in some ways.  We fix some of these issues
    in this file. *)

(** [intuition] means [intuition auto with *].  This is very wrong and
    fragile and slow.  We make [intuition] mean [intuition auto]. *)
Tactic Notation "intuition" tactic3(tactic) := intuition tactic.
Tactic Notation "intuition" := intuition auto.

(** A version of [intuition] that allows you to see how the old
    [intuition] tactic solves the proof. *)
Ltac debug_intuition := idtac "<infomsg>Warning: debug_intuition should not be used in production code.</infomsg>"; intuition debug auto with *.
