Require Import Crypto.Util.Tactics.EvarNormalize.
Require Import Crypto.Util.Tactics.ClearFree.

Ltac allow_debug_in_cache := constr:(false).

Ltac abstract_tac_with_debug abstract_tac tac arg :=
  let ctrue := constr:(true) in
  let cfalse := constr:(false) in
  let T := lazymatch goal with |- ?T => T end in
  let id' := fresh in
  simple notypeclasses refine (match _ : T return T with id' => _ end);
  [ lazymatch allow_debug_in_cache with
    | false => solve [ unshelve tac ]
    | true => tac; shelve
    | ?v => fail 1000 "Invalid non-bool value for allow_debug_in_cache" v "(" "expected" ctrue "or" cfalse ")"
    end
  | let res := (eval cbv delta [id'] in id') in
    clear id';
    lazymatch allow_debug_in_cache with
    | false
      => abstract_tac ltac:(exact_no_check res) arg
    | true
      => tryif abstract_tac ltac:(exact_no_check res) arg
        then idtac
        else exact res
    | ?v => fail 1000 "Invalid non-bool value for allow_debug_in_cache" v "(" "expected" ctrue "or" cfalse ")"
    end ].

Ltac cache_term_with_type_by_gen ty abstract_tac tac id :=
  let id' := fresh id in
  let __ := lazymatch goal with
            | [ |- ?T ]
              => simple notypeclasses refine (match _ : ty return T with id' => _ end);
                 [ abstract_tac_with_debug abstract_tac tac id'
                 | ]
            end in
  let ret := (eval cbv [id'] in id') in
  let __ := match goal with
            | _ => clear id'
            end in
  ret.

Ltac clear_cache_term_with_type_by do_clear ty tac id :=
  cache_term_with_type_by_gen ty ltac:(fun tac id' => do_clear (); transparent_abstract tac using id') ltac:(do_clear (); tac) id.
Ltac clear_cache_proof_with_type_by do_clear ty tac id :=
  cache_term_with_type_by_gen ty ltac:(fun tac id' => do_clear (); abstract tac using id') ltac:(do_clear (); tac) id.
Ltac cache_term_with_type_by ty tac id := clear_cache_term_with_type_by ltac:(fun _ => idtac) ty tac id.
Ltac cache_proof_with_type_by ty tac id := clear_cache_proof_with_type_by ltac:(fun _ => idtac) ty tac id.
Ltac cache_term_by tac id :=
  let ty := open_constr:(_) in
  cache_term_with_type_by ty tac id.
Ltac cache_proof_by ty tac id :=
  let ty := open_constr:(_) in
  cache_proof_with_type_by ty tac id.
Ltac cache_term term id :=
  let ty := type of term in
  let term := evar_normalize term in (* COQBUG(https://github.com/coq/coq/issues/10044) *)
  clear_cache_term_with_type_by ltac:(fun _ => clear_free term) ty ltac:(exact_no_check term) id.

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
          let tac :=
            refine (eq_rect _ P (proj2_sig id') _ _);
            red_cast_no_check (eq_refl v)
          in
          abstract_tac_with_debug ltac:(fun tac _ => abstract tac) tac ()
         )
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
          let tac _ :=
            refine (eq_rect _ P (proj2_sig id') _ _);
            red_cast_no_check (eq_refl v)
          in
          abstract_tac_with_debug ltac:(fun tac _ => abstract tac) tac ()
         )
           id.
Ltac cache_sig_with_type_by ty tac id
  := cache_sig_red_with_type_by ty tac ltac:(fun v => v) exact_no_check id.
Ltac cache_vm_sig_with_type_by ty tac id
  := cache_sig_red_with_type_by ty tac ltac:(fun v => eval vm_compute in v) vm_cast_no_check id.
Ltac cache_sig_with_type ty term id
  := cache_sig_red_with_type ty term ltac:(fun v => v) exact_no_check id.
Ltac cache_vm_sig_with_type ty term id
  := cache_sig_red_with_type ty term ltac:(fun v => eval vm_compute in v) vm_cast_no_check id.
