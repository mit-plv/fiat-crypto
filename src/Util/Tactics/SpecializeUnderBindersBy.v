Require Import Crypto.Util.Tactics.SpecializeBy.
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

Ltac guarded_specialize_hyp_under_binders_by guard_tac H tac :=
  idtac;
  let is_transparent := match goal with
                        | _ => let __ := (eval cbv delta [H] in H) in
                               constr:(true)
                        | _ => constr:(false)
                        end in
  lazymatch is_transparent with
  | true
    => let H' := fresh in
       rename H into H';
       let H'' := guarded_specialize_term_under_binders_by guard_tac H' tac in
       pose H'' as H;
       subst H'
  | false
    => let H := guarded_specialize_term_under_binders_by guard_tac H tac in
       specialize H
  end.

Ltac guard_noop H := idtac.

Ltac guard_nondep H :=
  lazymatch type of H with
  | ?A -> ?B => idtac
  end.

(** try to specialize all non-dependent hypotheses using [tac] at any point under their binders, maintaining transparency *)
Ltac guarded_specialize_under_binders_by' tac guard_tac :=
  idtac;
  match goal with
  | [ H : _ |- _ ]
    => guard_tac H;
       guarded_specialize_hyp_under_binders_by guard_nondep H tac
  end.
Ltac guarded_specialize_dep_under_binders_by' tac guard_tac :=
  idtac;
  match goal with
  | [ H : _ |- _ ]
    => guard_tac H;
       guarded_specialize_hyp_under_binders_by guard_noop H tac
  end.

Ltac specialize_under_binders_by' tac := guarded_specialize_under_binders_by' tac ltac:(fun _ => idtac).
Ltac specialize_dep_under_binders_by' tac := guarded_specialize_dep_under_binders_by' tac ltac:(fun _ => idtac).

Ltac guarded_specialize_under_binders_by tac guard_tac := repeat guarded_specialize_under_binders_by' tac guard_tac.
Ltac guarded_specialize_dep_under_binders_by tac guard_tac := repeat guarded_specialize_dep_under_binders_by' tac guard_tac.

Ltac specialize_under_binders_by tac := repeat specialize_under_binders_by' tac.
Ltac specialize_dep_under_binders_by tac := repeat specialize_dep_under_binders_by' tac.

(** [specialize_under_binders_by auto] should not mean [specialize_under_binders_by ( auto
    with * )]!!!!!!! (see
    https://coq.inria.fr/bugs/show_bug.cgi?id=4966) We fix this design
    flaw. *)
Tactic Notation "specialize_under_binders_by" tactic3(tac) := specialize_under_binders_by tac.
Tactic Notation "specialize_dep_under_binders_by" tactic3(tac) := specialize_dep_under_binders_by tac.
