Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.SideConditions.CorePackages.

Definition vm_decide_package (P : Prop) := P.
Definition cbv_minus_then_vm_decide_package {T} (ident : T) (P : Prop) := P.
Definition vm_compute_reflexivity_package (P : Prop) := P.
Inductive cast_bias := LHS | RHS.
Definition vm_compute_evar_package_gen {bias : cast_bias} {T} (v : T) :=
  @evar_package T v.
Notation vm_compute_evar_package_vm_small := (@vm_compute_evar_package_gen LHS).
Notation vm_compute_evar_package_vm_large := (@vm_compute_evar_package_gen RHS).
Notation vm_compute_evar_package := vm_compute_evar_package_vm_small.
Definition vm_cast_evar_package {s} (v : s) d := @evard_package s d v.
Definition cast_evar_package {s} (v : s) d := @evard_package s d v.

Ltac autosolve else_tac :=
  CorePackages.preautosolve ();
  lazymatch goal with
  | [ |- vm_decide_package ?P ] => cbv beta delta [vm_decide_package]; vm_decide
  | [ |- cbv_minus_then_vm_decide_package ?ident ?P ] => cbv -[ident]; vm_decide
  | [ |- vm_compute_reflexivity_package ?P ] => vm_compute; reflexivity
  | [ |- vm_compute_evar_package_vm_small ?v ]
    => let v' := (eval vm_compute in v) in
       (exists v'); abstract vm_cast_no_check (eq_refl v')
  | [ |- vm_compute_evar_package_vm_large ?v ]
    => let v' := (eval vm_compute in v) in
       (exists v'); abstract vm_cast_no_check (eq_refl v)
  | [ |- vm_cast_evar_package ?v ?d ]
    => unshelve eexists (v <: d);
       [ vm_compute; reflexivity
       | cbv beta;
         let lhs := lazymatch goal with |- ?lhs = _ => lhs end in
         abstract exact_no_check (eq_refl lhs) ]
  | [ |- cast_evar_package (s:=?s) ?v ?d ]
    => exact (@Build_evard_package
                s d v
                v eq_refl eq_refl)
  | _ => CorePackages.autosolve else_tac
  end.
