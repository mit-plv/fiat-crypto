Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.Head.

(** destruct discriminees of [match]es in the goal *)
(* Prioritize breaking apart things in the context, then things which
   don't need equations, then simple matches (which can be displayed
   as [if]s), and finally matches in general. *)
Ltac set_match_refl v' only_when :=
  lazymatch goal with
  | [ |- context G[match ?e with _ => _ end eq_refl] ]
    => only_when e;
       let T := fresh in
       evar (T : Type); evar (v' : T);
       subst T;
       let vv := (eval cbv delta [v'] in v') in
       let G' := context G[vv] in
       let G''' := context G[v'] in
       lazymatch goal with |- ?G'' => unify G' G'' end;
       change G'''
  end.
Ltac set_match_refl_hyp v' only_when :=
  lazymatch goal with
  | [ H : context G[match ?e with _ => _ end eq_refl] |- _ ]
    => only_when e;
       let T := fresh in
       evar (T : Type); evar (v' : T);
       subst T;
       let vv := (eval cbv delta [v'] in v') in
       let G' := context G[vv] in
       let G''' := context G[v'] in
       let G'' := type of H in
       unify G' G'';
       change G''' in H
  end.
Ltac destruct_by_existing_equation match_refl_hyp :=
  let v := (eval cbv delta [match_refl_hyp] in match_refl_hyp) in
  lazymatch v with
  | match ?e with _ => _ end (@eq_refl ?T ?e)
    => let H := fresh in
       let e' := fresh in
       pose e as e';
       change e with e' in (value of match_refl_hyp) at 1;
       first [ pose (@eq_refl T e : e = e') as H;
               change (@eq_refl T e) with H in (value of match_refl_hyp);
               clearbody H e'
             | pose (@eq_refl T e : e' = e) as H;
               change (@eq_refl T e) with H in (value of match_refl_hyp);
               clearbody H e' ];
       destruct e'; subst match_refl_hyp
  end.
Ltac destruct_rewrite_sumbool e :=
  let H := fresh in
  destruct e as [H|H];
  try lazymatch type of H with
      | ?LHS = ?RHS
        => lazymatch RHS with
           | context[LHS] => fail
           | _ => idtac
           end;
           rewrite ?H; rewrite ?H in *;
           repeat match goal with
                  | [ |- context G[LHS] ]
                    => let LHS' := fresh in
                       pose LHS as LHS';
                       let G' := context G[LHS'] in
                       change G';
                       replace LHS' with RHS by (subst LHS'; symmetry; apply H);
                       subst LHS'
                  end
      end.
Ltac break_match_step only_when :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ]
    => only_when e; is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ]
    => only_when e;
       match type of e with
       | sumbool _ _ => destruct_rewrite_sumbool e
       end
  | [ |- context[if ?e then _ else _] ]
    => only_when e; destruct e eqn:?
  | [ |- context[match ?e with _ => _ end] ]
    => only_when e; destruct e eqn:?
  | _ => let v := fresh in set_match_refl v only_when; destruct_by_existing_equation v
  end.
Ltac break_match_hyps_step only_when :=
  match goal with
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e; is_var e; destruct e
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e;
       match type of e with
       | sumbool _ _ => destruct_rewrite_sumbool e
       end
  | [ H : context[if ?e then _ else _] |- _ ]
    => only_when e; destruct e eqn:?
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e; destruct e eqn:?
  | _ => let v := fresh in set_match_refl_hyp v only_when; destruct_by_existing_equation v
  end.
Ltac break_match := repeat break_match_step ltac:(fun _ => idtac).
Ltac break_match_hyps := repeat break_match_hyps_step ltac:(fun _ => idtac).
Ltac break_match_when_head_step T :=
  break_match_step
    ltac:(fun e => let T' := type of e in
                   let T' := head T' in
                   constr_eq T T').
Ltac break_match_hyps_when_head_step T :=
  break_match_hyps_step
    ltac:(fun e => let T' := type of e in
                   let T' := head T' in
                   constr_eq T T').
Ltac break_match_when_head T := repeat break_match_when_head_step T.
Ltac break_match_hyps_when_head T := repeat break_match_hyps_when_head_step T.
Ltac break_innermost_match_step :=
  break_match_step ltac:(fun v => lazymatch v with
                                  | context[match _ with _ => _ end] => fail
                                  | _ => idtac
                                  end).
Ltac break_innermost_match_hyps_step :=
  break_match_hyps_step ltac:(fun v => lazymatch v with
                                       | context[match _ with _ => _ end] => fail
                                       | _ => idtac
                                       end).
Ltac break_innermost_match := repeat break_innermost_match_step.
Ltac break_innermost_match_hyps := repeat break_innermost_match_hyps_step.
