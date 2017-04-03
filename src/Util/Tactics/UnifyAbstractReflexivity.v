(** * Various variants on [reflexivity] and [abstract reflexivity] for evars *)
(** This file defines a number of different ways to solve goals of the
    form [LHS = RHS] where [LHS] may contain evars and [RHS] must not
    contain evars.  Most tactics use [abstract] to reduce the load on
    [Defined] and to catch looping behavior early. *)

(** This is the generic tactic; from a goal [LHS = RHS], it transforms
    the RHS with a passed transformer, unifies the output with LHS
    using the passed [unify] tactic, and then uses the passed variant
    of [exact_no_check] to [abstract] a subproof of the form [eq_refl
    new_rhs].  If there is no evar in the [LHS], don't run
    transformation nor unification. *)
Ltac unify_transformed_rhs_abstract_tac transform_rhs unify exact_no_check :=
  intros; clear;
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => tryif has_evar LHS
    then let RHS' := transform_rhs RHS in
         unify LHS RHS'; clear;
         abstract exact_no_check (eq_refl RHS')
    else abstract exact_no_check (eq_refl RHS)
  end.

Ltac idterm x := x.
Ltac noop2 x y := idtac.
Ltac eval_vm_compute_in x := eval vm_compute in x.
Ltac eval_compute_in x := eval vm_compute in x.
Ltac unify_tac x y := unify x y.

(** The tactic [abstract_vm_compute_rhs_reflexivity] unifies [LHS]
    with the result of [vm_compute]ing [RHS], and costs two
    [vm_compute]s, unless there is no evar in the [LHS], in which case
    it costs only one [vm_compute]. *)
Ltac unify_abstract_vm_compute_rhs_reflexivity :=
  unify_transformed_rhs_abstract_tac
    eval_vm_compute_in
    unify_tac
    vm_cast_no_check.
(** The tactic [abstract_compute_rhs_reflexivity] unfies [LHS] with
    the result of running [compute] in [RHS], and costs a [compute]
    and a [vm_compute].  Use this if you don't want to lose binder
    names or otherwise can't use [vm_compute]. *)
Ltac unify_abstract_compute_rhs_reflexivity :=
  unify_transformed_rhs_abstract_tac
    eval_compute_in
    unify_tac
    vm_cast_no_check.
(** The tactic [abstract_rhs_reflexivity] unifies [LHS] with [RHS]. *)
Ltac unify_abstract_rhs_reflexivity :=
  unify_transformed_rhs_abstract_tac
    idterm
    unify_tac
    exact_no_check.
