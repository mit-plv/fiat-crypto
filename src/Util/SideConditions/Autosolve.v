Import EqNotations.
Require Import Crypto.Util.Decidable.

Definition vm_decide_package (P : Prop) := P.
Definition cbv_minus_then_vm_decide_package {T} (ident : T) (P : Prop) := P.
Definition vm_compute_reflexivity_package (P : Prop) := P.
Record evar_package {T} (v : T) :=
  { val : T;
    evar_package_pf : val = v }.
Arguments val {T v} _.
Arguments evar_package_pf {T v} _.
Record evard_package {s d} (v : s) :=
  { vald : d;
    evard_package_pfT : s = d;
    evard_package_pf : vald = rew evard_package_pfT in v }.
Arguments vald {s d v} _.
Arguments evard_package_pfT {s d v} _.
Arguments evard_package_pf {s d v} _.
Inductive cast_bias := LHS | RHS.
Definition vm_compute_evar_package_gen {bias : cast_bias} {T} (v : T) :=
  @evar_package T v.
Notation vm_compute_evar_package_vm_small := (@vm_compute_evar_package_gen LHS).
Notation vm_compute_evar_package_vm_large := (@vm_compute_evar_package_gen RHS).
Notation vm_compute_evar_package := vm_compute_evar_package_vm_small.
Definition vm_cast_evar_package {s} (v : s) d := @evard_package s d v.
Definition cast_evar_package {s} (v : s) d := @evard_package s d v.

Module Internal.
  Ltac autosolve else_tac :=
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
      => simple refine {| vald := (v <: d) |};
         [ vm_compute; reflexivity
         | let lhs := lazymatch goal with |- ?lhs = _ => lhs end in
           abstract exact_no_check (eq_refl lhs) ]
    | [ |- cast_evar_package (s:=?s) ?v ?d ]
      => exact (@Build_evard_package
                  s d v
                  v eq_refl eq_refl)
    | _ => else_tac ()
    end.
End Internal.

Ltac autosolve := Internal.autosolve.
