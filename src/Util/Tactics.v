(** * Generic Tactics *)

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.
(* [assert T], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "assert" constr(T) :=
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => assert T
  end.

(* [assert T], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "assert" constr(T) "by" tactic3(tac) :=
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => assert T by tac
  end.
