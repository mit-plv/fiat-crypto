(** * Machinery for reimplementing some bits of [rewrite_strat] with open pattern databases *)
Require Import Crypto.Util.Notations.
(** We build classes for rewriting in each direction, and pick lemmas
    by resolving on tags and the term to be rewritten. *)
(** Base class, for bidirectional rewriting. *)
Class rewrite_eq {tagT} (tag : tagT) {A} (x y : A)
  := by_rewrite : x = y.
Arguments by_rewrite {tagT} tag {A} _ _ {_}.
Infix "<~=~>" := (rewrite_eq _) : type_scope.

Class rewrite_right_to_left_eq {tagT} (tag : tagT) {A} (x y : A)
  := by_rewrite_right_to_left : rewrite_eq tag x y.
Arguments by_rewrite_right_to_left {tagT} tag {A} _ _ {_}.
Global Instance unfold_rewrite_right_to_left_eq {tagT tag A x y} (H : @rewrite_eq tagT tag A x y)
  : @rewrite_right_to_left_eq tagT tag A x y := H.
Infix "<~=" := (rewrite_right_to_left_eq _) : type_scope.

Class rewrite_left_to_right_eq {tagT} (tag : tagT) {A} (x y : A)
  := by_rewrite_left_to_right : rewrite_eq tag x y.
Arguments by_rewrite_left_to_right {tagT} tag {A} _ _ {_}.
Global Instance unfold_rewrite_left_to_right_eq {tagT tag A x y} (H : @rewrite_eq tagT tag A x y)
  : @rewrite_left_to_right_eq tagT tag A x y := H.
Infix "=~>" := (rewrite_left_to_right_eq _) : type_scope.

Ltac typeclass_do_left_to_right tag from tac :=
  let lem := constr:(by_rewrite_left_to_right tag from _ : from = _) in tac lem.
Ltac typeclass_do_right_to_left tag from tac :=
  let lem := constr:(by_rewrite_right_to_left tag _ from : _ = from) in tac lem.


Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" open_constr(from) "->" :=
  typeclass_do_left_to_right tag from ltac:(fun lem => rewrite -> lem).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" open_constr(from) "->" "in" "*" :=
  typeclass_do_left_to_right tag from ltac:(fun lem => rewrite -> lem in * ).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" open_constr(from) "->" "in" hyp_list(H) :=
  typeclass_do_left_to_right tag from ltac:(fun lem => rewrite -> lem in H).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" open_constr(from) "->" "in" hyp_list(H) "|-" "*" :=
  typeclass_do_left_to_right tag from ltac:(fun lem => rewrite -> lem in H |- *).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" open_constr(from) "->" "in" "*" "|-" "*" :=
  typeclass_do_left_to_right tag from ltac:(fun lem => rewrite -> lem in * |- * ).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" open_constr(from) "->" "in" "*" "|-" :=
  typeclass_do_left_to_right tag from ltac:(fun lem => rewrite -> lem in * |- ).


Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" "<-" open_constr(from) :=
  typeclass_do_right_to_left tag from ltac:(fun lem => rewrite <- lem).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" "<-" open_constr(from) "in" "*" :=
  typeclass_do_right_to_left tag from ltac:(fun lem => rewrite <- lem in * ).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" "<-" open_constr(from) "in" hyp_list(H) :=
  typeclass_do_right_to_left tag from ltac:(fun lem => rewrite <- lem in H).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" "<-" open_constr(from) "in" hyp_list(H) "|-" "*" :=
  typeclass_do_right_to_left tag from ltac:(fun lem => rewrite <- lem in H |- *).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" "<-" open_constr(from) "in" "*" "|-" "*" :=
  typeclass_do_right_to_left tag from ltac:(fun lem => rewrite <- lem in * |- * ).
Tactic Notation "tc_rewrite" "(" open_constr(tag) ")" "<-" open_constr(from) "in" "*" "|-" :=
  typeclass_do_right_to_left tag from ltac:(fun lem => rewrite <- lem in * |- ).
