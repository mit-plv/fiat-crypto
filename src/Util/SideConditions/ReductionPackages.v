Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.Tactics.HeadUnderBinders.

Definition vm_decide_package (P : Prop) := P.
Definition cbv_minus_then_vm_decide_package {T} (ident : T) (P : Prop) := P.
Definition vm_compute_reflexivity_package (P : Prop) := P.
Inductive cast_bias := LHS | RHS.
Definition vm_compute_evar_package_gen {bias : cast_bias} {T} (v : T) :=
  @evar_package T v.
Notation vm_compute_evar_package_vm_small := (@vm_compute_evar_package_gen LHS).
Notation vm_compute_evar_package_vm_large := (@vm_compute_evar_package_gen RHS).
Notation vm_compute_evar_package := vm_compute_evar_package_vm_small.
Definition vm_compute_cbv_evar_package_gen {bias : cast_bias} {T} (v : T) :=
  @evar_package T v.
Notation vm_compute_cbv_evar_package_vm_small := (@vm_compute_cbv_evar_package_gen LHS).
Notation vm_compute_cbv_evar_package_vm_large := (@vm_compute_cbv_evar_package_gen RHS).
Notation vm_compute_cbv_evar_package := vm_compute_cbv_evar_package_vm_small.
Definition vm_cast_evar_package {s} (v : s) d := @evard_package s d v.
Definition cast_evar_package {s} (v : s) d := @evard_package s d v.
Definition vm_compute_cast_evar_package {s} (v : s) d := @evard_package s d v.

Definition optional_evar_Prop_package {T} (P : T -> Prop) (alt_pkg : Type)
  := @evar_Prop_package
       (option T)
       (fun v => match v with
                 | Some v => P v
                 | None => True
                 end).

Definition None_evar_Prop_package' {alt_pkg T P} : @optional_evar_Prop_package T P alt_pkg
  := {| val := None ; evar_package_pf := I |}.
Notation None_evar_Prop_package := (@None_evar_Prop_package' unit).

Notation optional_evar_package pkg_type
  := (optional_evar_Prop_package
        (ltac:(lazymatch eval hnf in pkg_type with evar_Prop_package ?P => exact P end))
        pkg_type)
       (only parsing).

Definition option_evar_rel_package {A} (v : option A) B (R : B -> A -> Prop) (alt_pkg : A -> Type)
  := @evar_Prop_package
       (option B)
       (fun v' => match v', v with
                  | Some v', Some v => R v' v
                  | None, None => True
                  | Some _, None | None, Some _ => False
                  end).

Notation optional_evar_rel_package pkg_type x
  := (option_evar_rel_package
        x
        _
        (fun a b
         => ltac:(lazymatch eval hnf in (pkg_type b) with
                  | evar_Prop_package ?P
                    => let P := (eval cbv beta in (P a)) in
                       exact P
                  end))
        pkg_type)
       (only parsing).

Definition unoption_evar_rel_package {A v B R alt_pkg}
           (f : forall v, alt_pkg v -> @evar_rel_package A v B R)
  : forall (pkg : match v with
                  | Some v => alt_pkg v
                  | None => True
                  end),
    @option_evar_rel_package A v B R alt_pkg
  := match v
           return match v with
                  | Some v => alt_pkg v
                  | None => True
                  end -> @option_evar_rel_package A v B R alt_pkg
     with
     | Some v => fun pkg => {| val := Some (val (f _ pkg));
                               evar_package_pf := evar_package_pf (f _ pkg) |}
     | None => fun _ => None_evar_Prop_package
     end.

Ltac autosolve autosolve_tac else_tac :=
  lazymatch goal with
  | [ |- match ?x with Some _ => _ | None => _ end ]
    => let x' := (eval hnf in x) in
       progress change x with x';
       cbv beta iota;
       autosolve_tac else_tac
  | [ |- vm_decide_package ?P ] => cbv beta delta [vm_decide_package]; vm_decide
  | [ |- cbv_minus_then_vm_decide_package ?ident ?P ] => cbv -[ident]; vm_decide
  | [ |- vm_compute_reflexivity_package ?P ] => vm_compute; reflexivity
  | [ |- vm_compute_evar_package_vm_small ?v ]
    => let v' := (eval vm_compute in v) in
       (exists v'); abstract vm_cast_no_check (eq_refl v')
  | [ |- vm_compute_evar_package_vm_large ?v ]
    => let v' := (eval vm_compute in v) in
       (exists v'); abstract vm_cast_no_check (eq_refl v)
  | [ |- vm_compute_cbv_evar_package_vm_small ?v ]
    => let v' := (eval vm_compute in v) in
       let v' := (eval cbv in v) in
       (exists v'); abstract vm_cast_no_check (eq_refl v')
  | [ |- vm_compute_cbv_evar_package_vm_large ?v ]
    => let v' := (eval vm_compute in v) in
       let v' := (eval cbv in v) in
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
  | [ |- vm_compute_cast_evar_package (s:=?s) ?v ?d ]
    => let v' := (eval vm_compute in v) in
       exact (@Build_evard_package
                s d v
                v' eq_refl eq_refl)
  | [ |- @option_evar_rel_package ?A ?v ?B ?R ?alt_pkg ]
    => refine (@unoption_evar_rel_package A v B R alt_pkg (fun _ x => x) _);
       autosolve_tac else_tac
  | _ => else_tac ()
  end.
