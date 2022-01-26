Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.FindHyp.

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  tryif let H := find_hyp T in fail 2 "Already a hypothesis" H "of type" T
  then fail
  else pose proof defn.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  tryif let H := find_hyp_with_body defn in fail 2 "Already a hypothesis" H "with body" defn
  then fail
  else pose defn.

(** [assert T], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "assert" constr(T) :=
  tryif let H := find_hyp T in fail 2 "Already a hypothesis" H "of type" T
  then fail
  else assert T.

(** [assert T], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "assert" constr(T) "by" tactic3(tac) :=
  tryif let H := find_hyp T in fail 2 "Already a hypothesis" H "of type" T
  then fail
  else assert T by tac.
