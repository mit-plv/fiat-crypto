Require Import Crypto.Util.Tactics.TransparentAssert.

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
  cache_term_with_type_by ty ltac:(exact_no_check term) id.
