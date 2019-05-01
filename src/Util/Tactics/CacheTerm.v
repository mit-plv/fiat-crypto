Require Import Crypto.Util.Tactics.TransparentAssert.
Require Import Crypto.Util.Tactics.EvarNormalize.

Ltac cache_term_with_type_by_gen ty abstract_tac id :=
  let id' := fresh id in
  let dummy := match goal with
               | _ => transparent assert ( id' : ty );
                      [ abstract_tac id'
                      | ]
               end in
  let ret := (eval cbv [id'] in id') in
  let dummy := match goal with
               | _ => clear id'
               end in
  ret.
Ltac cache_term_with_type_by ty tac id :=
  cache_term_with_type_by_gen ty ltac:(fun id' => transparent_abstract tac using id') id.
Ltac cache_proof_with_type_by ty tac id :=
  cache_term_with_type_by_gen ty ltac:(fun id' => abstract tac using id') id.
Ltac cache_term_by tac id :=
  let ty := open_constr:(_) in
  cache_term_with_type_by ty tac id.
Ltac cache_proof_by ty tac id :=
  let ty := open_constr:(_) in
  cache_proof_with_type_by ty tac id.
Ltac cache_term term id :=
  let ty := type of term in
  let term := evar_normalize term in (* COQBUG(https://github.com/coq/coq/issues/10044) *)
  cache_term_with_type_by ty ltac:(exact_no_check term) id.

Ltac cache_sig_red_with_type_by ty tac red_tac red_cast_no_check id :=
  let id' := fresh id in
  let id' := fresh id in
  let id' := cache_term_with_type_by ty tac id' in
  let P := lazymatch ty with sig ?P => P end in
  cache_term_with_type_by
    ty
    ltac:(let v := (eval cbv beta iota delta [id' proj1_sig] in (proj1_sig id')) in
          let v := red_tac v in
          (exists v);
          abstract (
              refine (eq_rect _ P (proj2_sig id') _ _);
              red_cast_no_check (eq_refl v)
            ))
           id.
Ltac cache_sig_red_with_type ty term red_tac red_cast_no_check id :=
  let id' := fresh id in
  let id' := fresh id in
  let id' := cache_term term id' in
  let P := lazymatch ty with sig ?P => P end in
  cache_term_with_type_by
    ty
    ltac:(let v := (eval cbv beta iota delta [id' proj1_sig] in (proj1_sig id')) in
          let v := red_tac v in
          (exists v);
          abstract (
              refine (eq_rect _ P (proj2_sig id') _ _);
              red_cast_no_check (eq_refl v)
            ))
           id.
Ltac cache_sig_with_type_by ty tac id
  := cache_sig_red_with_type_by ty tac ltac:(fun v => v) exact_no_check id.
Ltac cache_vm_sig_with_type_by ty tac id
  := cache_sig_red_with_type_by ty tac ltac:(fun v => eval vm_compute in v) vm_cast_no_check id.
Ltac cache_sig_with_type ty term id
  := cache_sig_red_with_type ty term ltac:(fun v => v) exact_no_check id.
Ltac cache_vm_sig_with_type ty term id
  := cache_sig_red_with_type ty term ltac:(fun v => eval vm_compute in v) vm_cast_no_check id.
