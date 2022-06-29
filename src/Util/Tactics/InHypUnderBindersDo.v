Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.GeneralizeOverHoles.
Require Import Crypto.Util.Tactics.UniquePose.

Ltac guarded_in_hyp_term_under_binders_do' guard_tac H tac :=
  let is_transparent := match goal with
                        | _ => let __ := (eval cbv delta [H] in H) in
                               constr:(true)
                        | _ => constr:(false)
                        end in
  let __ := lazymatch goal with _ => guard_tac H end in
  match goal with
  | _ => let __ := lazymatch goal with _ => progress tac H end in
         H
  | _ => let __ := lazymatch is_transparent with
                   | true => let H' := fresh in
                             rename H into H';
                             let v := open_constr:(_) in
                             pose (H' v) as H;
                             subst H'
                   | false
                     => (* kludge for old Coq *)
                       (*let v := open_constr:(_) in*)
                       let t := open_constr:(_) in
                       let v := fresh in
                       evar (v : t);
                       specialize (H v);
                       subst v
                   end in
         guarded_in_hyp_term_under_binders_do' guard_tac H tac
  end.

Ltac guarded_in_hyp_term_under_binders_do guard_tac H tac :=
  generalize_over_holes ltac:(fun _ => guarded_in_hyp_term_under_binders_do' guard_tac H tac).

Ltac guarded_in_hyp_gen_hyp_under_binders_do all_ways guard_tac H tac :=
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
       let H'' := guarded_in_hyp_term_under_binders_do guard_tac H' tac in
       pose H'' as H;
       subst H'
  | (true, true)
    => let H := guarded_in_hyp_term_under_binders_do guard_tac H tac in
       unique pose H
  | (false, false)
    => let H' := fresh in
       rename H into H';
       let H'' := guarded_in_hyp_term_under_binders_do guard_tac H' tac in
       pose proof H'' as H;
       clear H'
  | (true, false)
    => let H := guarded_in_hyp_term_under_binders_do guard_tac H tac in
       unique pose proof H
  end.

Ltac guarded_in_hyp_hyp_under_binders_do guard_tac H tac :=
  guarded_in_hyp_gen_hyp_under_binders_do false guard_tac H tac.
Ltac guarded_in_hyp_hyp_all_ways_under_binders_do guard_tac H tac :=
  guarded_in_hyp_gen_hyp_under_binders_do true guard_tac H tac.

Ltac guard_noop H := idtac.

Ltac guarded_in_hyp_gen_under_binders_do' all_ways tac guard_tac :=
  idtac;
  match goal with
  | [ H : _ |- _ ]
    => guard_tac H;
       guarded_in_hyp_gen_hyp_under_binders_do all_ways guard_noop H tac
  end.

Ltac guarded_in_hyp_under_binders_do' tac guard_tac :=
  guarded_in_hyp_gen_under_binders_do' false tac guard_tac.

Ltac in_hyp_gen_under_binders_do' all_ways tac := guarded_in_hyp_gen_under_binders_do' all_ways tac ltac:(fun _ => idtac).

Ltac in_hyp_under_binders_do' tac := in_hyp_gen_under_binders_do' false tac.

Ltac guarded_in_hyp_gen_under_binders_do all_ways tac guard_tac := repeat guarded_in_hyp_gen_under_binders_do' all_ways tac guard_tac.

Ltac guarded_in_hyp_under_binders_do tac guard_tac := guarded_in_hyp_gen_under_binders_do false tac guard_tac.

Ltac guarded_in_hyp_all_ways_under_binders_do tac guard_tac := guarded_in_hyp_gen_under_binders_do true tac guard_tac.

Ltac in_hyp_gen_under_binders_do all_ways tac := repeat in_hyp_gen_under_binders_do' all_ways tac.

Ltac in_hyp_under_binders_do tac := in_hyp_gen_under_binders_do false tac.

Ltac in_hyp_all_ways_under_binders_do tac := in_hyp_gen_under_binders_do true tac.

(** [in_hyp_under_binders_do auto] should not mean [in_hyp_under_binders_do ( auto
    with * )]!!!!!!! (see
    https://coq.inria.fr/bugs/show_bug.cgi?id=4966) We fix this design
    flaw. *)
Tactic Notation "in_hyp_under_binders_do" tactic3(tac) := in_hyp_under_binders_do tac.

Tactic Notation "in_hyp_all_ways_under_binders_do" tactic3(tac) := in_hyp_all_ways_under_binders_do tac.
