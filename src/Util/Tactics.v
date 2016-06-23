(** * Generic Tactics *)

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail 0 tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

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

(** destruct discriminees of [match]es in the goal *)
Ltac break_match_step :=
  match goal with
  | [ |- appcontext[match ?e with _ => _ end] ]
    => match type of e with
       | sumbool _ _ => destruct e
       | _ => is_var e; destruct e
       | _ => destruct e eqn:?
       end
  end.
Ltac break_match := repeat break_match_step.

Ltac free_in x y :=
  idtac;
  match y with
    | appcontext[x] => fail 1 x "appears in" y
    | _ => idtac
  end.

Ltac setoid_subst'' R x :=
  is_var x;
  match goal with
  | [ H : R x ?y |- _ ]
    => free_in x y; rewrite ?H in *; clear x H
  | [ H : R ?y x |- _ ]
    => free_in x y; rewrite <- ?H in *; clear x H
  end.

Ltac setoid_subst' x :=
  is_var x;
  match goal with
  | [ H : ?R x _ |- _ ] => setoid_subst'' R x
  | [ H : ?R _ x |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel' R :=
  idtac;
  match goal with
  | [ H : R ?x _ |- _ ] => setoid_subst'' R x
  | [ H : R _ ?x |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel R := repeat setoid_subst_rel' R.

Ltac setoid_subst_all :=
  repeat match goal with
         | [ H : ?R ?x ?y |- _ ] => is_var x; setoid_subst'' R x
         | [ H : ?R ?x ?y |- _ ] => is_var y; setoid_subst'' R y
         end.

Tactic Notation "setoid_subst" ident(x) := setoid_subst' x.
Tactic Notation "setoid_subst" := setoid_subst_all.

Ltac destruct_trivial_step :=
  match goal with
  | [ H : unit |- _ ] => clear H || destruct H
  | [ H : True |- _ ] => clear H || destruct H
  end.
Ltac destruct_trivial := repeat destruct_trivial_step.
