Require Import Coq.Classes.RelationClasses.

Tactic Notation "etransitivity" open_constr(y) :=
  intros;
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].
(** We call [Coq.Init.Notations.etransitivity] for compatibility
    because it's more powerful than [etransitivity _] in some cases,
    e.g., when things need to be unfolded. *)
Tactic Notation "etransitivity" := Coq.Init.Notations.etransitivity.
Tactic Notation "etransitivity_rev" uconstr(y) := [ > etransitivity y; cycle 1.. ].
Tactic Notation "etransitivity_rev" := [ > etransitivity; cycle 1.. ].

Ltac transitivity_rev y := [ > transitivity y; cycle 1.. ].
