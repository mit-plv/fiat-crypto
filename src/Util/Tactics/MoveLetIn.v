(** * Tactics for moving around [let ... in ...] and [dlet ... in ...] *)
Require Import Crypto.Util.LetIn.
(** The tactic [sig_dlet_in_rhs_to_context] moves to the context any
    [dlet x := y in ...] on the rhs of a goal of the form [{ a | lhs =
    rhs }]. *)
Ltac sig_dlet_in_rhs_to_context_step v :=
  lazymatch goal with
  | [ |- { a | _ = @Let_In ?A ?B ?x _ } ]
    => pose x as v;
       change (@Let_In A B x) with (fun P : forall a : A, B a => P v);
       cbv beta
  end.
Ltac sig_dlet_in_rhs_to_context :=
  repeat let v := fresh "x" in sig_dlet_in_rhs_to_context_step v.
(** The tactic [sig_dlet_in_lhs_to_context] moves to the context any
    [dlet x := y in ...] on the lhs of a goal of the form [{ a | lhs =
    rhs }]. *)
Ltac sig_dlet_in_lhs_to_context_step v :=
  lazymatch goal with
  | [ |- { a | @Let_In ?A ?B ?x _ = _ } ]
    => pose x as v;
       change (@Let_In A B x) with (fun P : forall a : A, B a => P v);
       cbv beta
  end.
Ltac sig_dlet_in_lhs_to_context :=
  repeat let v := fresh "x" in sig_dlet_in_lhs_to_context_step v.
(** The tactic [goal_dlet_to_context] moves to the context any
    [dlet x := y in ...] in the goal. *)
Ltac goal_dlet_to_context_step v :=
  match goal with
  | [ |- context[@Let_In ?A ?B ?x] ]
    => pose x as v;
       change (@Let_In A B x) with (fun P : forall a : A, B a => P v);
       cbv beta
  end.
Ltac goal_dlet_to_context :=
  repeat let v := fresh "x" in goal_dlet_to_context_step v.
(** Takes in a uconstr [uc], uses [set] to find it in the goal and
    passes the constr that it finds to [k] *)
Local Ltac with_uconstr_in_goal uc k :=
  let f := fresh in
  set (f := uc);
  let f' := (eval cbv delta [f] in f) in
  subst f; k f'.
(** This tactic creates a [dlet x := f in rhs] in the rhs of a goal
    of the form [lhs = rhs]. *)
Ltac context_to_dlet_in_rhs f :=
  lazymatch goal with
  | [ |- ?R ?LHS ?RHS ]
    => with_uconstr_in_goal
         f
         ltac:(fun f
               => let RHS' := lazymatch (eval pattern f in RHS) with
                              | ?RHS _ => RHS
                              end in
                  let x := fresh "x" in
                  transitivity (dlet x := f in RHS' x);
                  [ | clear; abstract (cbv [Let_In]; reflexivity) ]
              )
  end.
Tactic Notation "context_to_dlet_in_rhs" uconstr(f) := context_to_dlet_in_rhs f.
