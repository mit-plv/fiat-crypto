Import EqNotations.

Local Set Primitive Projections.

Create HintDb autosolve discriminated.

Definition raw_evar_package (T : Type) := T.

Record evar_Prop_package {T} (P : T -> Prop) :=
  { val :> raw_evar_package T;
    evar_package_pf : P val }.
Arguments val {T P} _.
Arguments evar_package_pf {T P} _.

Definition evar_package {T} (v : T)
  := @evar_Prop_package T (fun val => val = v).
Definition evar_package_pf_eq {T v} (pkg : @evar_package T v)
  : val pkg = v
  := Eval hnf in evar_package_pf pkg.

Definition evar_rel_package {A} (v : A) B (R : B -> A -> Prop)
  := @evar_Prop_package B (fun val => R val v).
Definition evar_package_pf_rel {A v B R} (pkg : @evar_rel_package A v B R)
  : R (val pkg) v
  := Eval hnf in evar_package_pf pkg.

Definition evard_package {s d} (v : s)
  := @evar_rel_package
       s
       v
       d
       (fun vald v => { pf : s = d | vald = rew pf in v }).
Definition Build_evard_package {s d} (v : s)
           (vald : d)
           (evard_package_pfT : s = d)
           (evard_package_pf : vald = rew evard_package_pfT in v)
  : @evard_package s d v
  := {| evar_package_pf := exist _ evard_package_pfT evard_package_pf |}.
Definition evard_package_pfT {s d v} (pkg : @evard_package s d v)
  : s = d
  := Eval cbv [proj1_sig evar_package_pf] in proj1_sig (evar_package_pf pkg).
Definition evard_package_pf {s d v} (pkg : @evard_package s d v)
  : val pkg = rew (evard_package_pfT pkg) in v
  := Eval cbv [proj1_sig evar_package_pf] in proj2_sig (evar_package_pf pkg).

Ltac preautosolve _ :=
  repeat autounfold with autosolve in *.

Module Internal.
  Ltac autosolve else_tac :=
    lazymatch goal with
    | [ |- True ] => exact I
    | [ |- unit ] => exact tt
    | [ |- IDProp ] => exact idProp
    | _ => else_tac ()
    end.
End Internal.

Ltac autosolve else_tac := else_tac ().
