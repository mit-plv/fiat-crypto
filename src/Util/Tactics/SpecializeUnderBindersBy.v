Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.GeneralizeOverHoles.

Ltac guarded_specialize_term_under_binders_by' guard_tac H tac :=
  lazymatch type of H with
  | forall a, _
    => match goal with
       | _ => let __ := lazymatch goal with _ => guard_tac H end in
              open_constr:(H ltac:(progress tac))
       | _ => let H := open_constr:(H _) in
              guarded_specialize_term_under_binders_by' guard_tac H tac
       end
  end.

Ltac guarded_specialize_term_under_binders_by guard_tac H tac :=
  generalize_over_holes ltac:(fun _ => guarded_specialize_term_under_binders_by' guard_tac H tac).

Ltac guarded_specialize_gen_hyp_under_binders_by all_ways guard_tac H tac :=
  idtac;
  let is_transparent := match goal with
                        | _ => let __ := (eval cbv delta [H] in H) in
                               constr:(true)
                        | _ => constr:(false)
                        end in
  lazymatch constr:((all_ways, is_transparent)) with
  | (false, true)
    => let H' := fresh in
       rename H into H';
       let H'' := guarded_specialize_term_under_binders_by guard_tac H' tac in
       pose H'' as H;
       subst H'
  | (true, true)
    => let H := guarded_specialize_term_under_binders_by guard_tac H tac in
       unique pose H
  | (false, false)
    => let H := guarded_specialize_term_under_binders_by guard_tac H tac in
       specialize H
  | (true, false)
    => let H := guarded_specialize_term_under_binders_by guard_tac H tac in
       unique pose proof H
  end.

Ltac guarded_specialize_hyp_under_binders_by guard_tac H tac :=
  guarded_specialize_gen_hyp_under_binders_by false guard_tac H tac.
Ltac guarded_specialize_hyp_all_ways_under_binders_by guard_tac H tac :=
  guarded_specialize_gen_hyp_under_binders_by true guard_tac H tac.

Ltac guard_noop H := idtac.

Ltac guard_nondep H :=
  lazymatch type of H with
  | ?A -> ?B => idtac
  end.

(** try to specialize all non-dependent hypotheses using [tac] at any point under their binders, maintaining transparency *)
Ltac guarded_specialize_gen_under_binders_by' all_ways tac guard_tac :=
  idtac;
  match goal with
  | [ H : _ |- _ ]
    => guard_tac H;
       guarded_specialize_gen_hyp_under_binders_by all_ways guard_nondep H tac
  end.
Ltac guarded_specialize_gen_dep_under_binders_by' all_ways tac guard_tac :=
  idtac;
  match goal with
  | [ H : _ |- _ ]
    => guard_tac H;
       guarded_specialize_gen_hyp_under_binders_by all_ways guard_noop H tac
  end.

Ltac guarded_specialize_under_binders_by' tac guard_tac :=
  guarded_specialize_gen_under_binders_by' false tac guard_tac.
Ltac guarded_specialize_dep_under_binders_by' tac guard_tac :=
  guarded_specialize_gen_dep_under_binders_by' false tac guard_tac.

Ltac specialize_gen_under_binders_by' all_ways tac := guarded_specialize_gen_under_binders_by' all_ways tac ltac:(fun _ => idtac).
Ltac specialize_gen_dep_under_binders_by' all_ways tac := guarded_specialize_gen_dep_under_binders_by' all_ways tac ltac:(fun _ => idtac).

Ltac specialize_under_binders_by' tac := specialize_gen_under_binders_by' false tac.
Ltac specialize_dep_under_binders_by' tac := specialize_gen_dep_under_binders_by' false tac.

Ltac guarded_specialize_gen_under_binders_by all_ways tac guard_tac := repeat guarded_specialize_gen_under_binders_by' all_ways tac guard_tac.
Ltac guarded_specialize_gen_dep_under_binders_by all_ways tac guard_tac := repeat guarded_specialize_gen_dep_under_binders_by' all_ways tac guard_tac.

Ltac guarded_specialize_under_binders_by tac guard_tac := guarded_specialize_gen_under_binders_by false tac guard_tac.
Ltac guarded_specialize_dep_under_binders_by tac guard_tac := guarded_specialize_gen_dep_under_binders_by false tac guard_tac.

Ltac guarded_specialize_all_ways_under_binders_by tac guard_tac := guarded_specialize_gen_under_binders_by true tac guard_tac.
Ltac guarded_specialize_all_ways_dep_under_binders_by tac guard_tac := guarded_specialize_gen_dep_under_binders_by true tac guard_tac.

Ltac specialize_gen_under_binders_by all_ways tac := repeat specialize_gen_under_binders_by' all_ways tac.
Ltac specialize_gen_dep_under_binders_by all_ways tac := repeat specialize_gen_dep_under_binders_by' all_ways tac.

Ltac specialize_under_binders_by tac := specialize_gen_under_binders_by false tac.
Ltac specialize_dep_under_binders_by tac := specialize_gen_dep_under_binders_by false tac.

Ltac specialize_all_ways_under_binders_by tac := specialize_gen_under_binders_by true tac.
Ltac specialize_all_ways_dep_under_binders_by tac := specialize_gen_dep_under_binders_by true tac.

(** [specialize_under_binders_by auto] should not mean [specialize_under_binders_by ( auto
    with * )]!!!!!!! (see
    https://coq.inria.fr/bugs/show_bug.cgi?id=4966) We fix this design
    flaw. *)
Tactic Notation "specialize_under_binders_by" tactic3(tac) := specialize_under_binders_by tac.
Tactic Notation "specialize_dep_under_binders_by" tactic3(tac) := specialize_dep_under_binders_by tac.

Tactic Notation "specialize_all_ways_under_binders_by" tactic3(tac) := specialize_all_ways_under_binders_by tac.
Tactic Notation "specialize_all_ways_dep_under_binders_by" tactic3(tac) := specialize_all_ways_dep_under_binders_by tac.
