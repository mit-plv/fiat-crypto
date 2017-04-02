(** * Reflective Pipeline: Glue Code *)
(** This file defines the tactics that transform a non-reflective goal
    into a goal the that the reflective machinery can handle. *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Curry.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tuple.

Module Export Exports.
  Export Crypto.Reflection.Z.Reify. (* export for the tactic redefinitions *)
End Exports.

(** The [do_curry] tactic takes a goal of the form
<<
BoundedWordToZ (?f a b ... z) = F A B ... Z
>>
    and turns it into a goal of the form
<<
BoundedWordToZ (f' (a, b, ..., z)) = F' (A, B, ..., Z)
>>
 *)
Ltac do_curry :=
  lazymatch goal with
  | [ |- ?BWtoZ ?f_bw = ?f_Z ]
    => let f_bw := head f_bw in
       let f_Z := head f_Z in
       change_with_curried f_Z;
       let f_bw_name := fresh f_bw in
       set (f_bw_name := f_bw);
       change_with_curried f_bw_name
  end.
(** The [split_BoundedWordToZ] tactic takes a goal of the form
<<
BoundedWordToZ (f args) = F ARGS
>>
    and splits it into a conjunction, one part about the computational
    behavior, and another part about the boundedness.  *)
Ltac count_tuple_length T :=
  lazymatch T with
  | (?A * ?B)%type => let a := count_tuple_length A in
                      let b := count_tuple_length B in
                      (eval compute in (a + b)%nat)
  | _ => constr:(1%nat)
  end.
Ltac make_evar_for_first_projection :=
  lazymatch goal with
  | [ |- @map ?N1 ?A ?B wordToZ (@proj1_sig _ ?P ?f) = ?fZ ?argsZ ]
    => let T := type of argsZ in
       let N := count_tuple_length T in
       let map' := (eval compute in (@map N)) in
       let proj1_sig' := (eval compute in @proj1_sig) in
       let f1 := fresh f in
       let f2 := fresh f in
       let pf := fresh in
       revert f; refine (_ : let f := exist P _ _ in _);
       intro f;
       pose (proj1_sig f) as f1;
       pose (proj2_sig f : P f1) as f2;
       change f with (exist _ f1 f2);
       subst f; cbn [proj1_sig proj2_sig] in f1, f2 |- *; revert f2;
       lazymatch goal with
       | [ |- let f' := _ in @?P f' ]
         => refine (let pf := _ in (proj2 pf : let f' := proj1 pf in P f'))
       end
  end.
Ltac split_BoundedWordToZ :=
  match goal with
  | [ |- BoundedWordToZ _ _ _ ?x = _ ]
    => revert x
  end;
  repeat match goal with
         | [ |- context[BoundedWordToZ _ _ _ ?x] ]
           => is_var x;
              first [ clearbody x; fail 1
                    | instantiate (1:=ltac:(destruct x)); destruct x ]
         end;
  cbv beta iota; intro;
  unfold BoundedWordToZ; cbn [proj1_sig];
  make_evar_for_first_projection.
(** The [zrange_to_reflective] tactic takes a goal of the form
<<
is_bounded_by _ bounds (map wordToZ (?fW args)) /\ map wordToZ (?fW args) = fZ argsZ
>>
    and uses [cut] and a small lemma to turn it into a goal that the
    reflective machinery can handle.  The goal left by this tactic
    should be fully solvable by the reflective pipeline. *)

Ltac const_tuple T val :=
  lazymatch T with
  | (?A * ?B)%type => let a := const_tuple A val in
                      let b := const_tuple B val in
                      constr:((a, b)%core)
  | _ => val
  end.
Lemma adjust_goal_for_reflective {T P} (LHS RHS : T)
  : P RHS /\ LHS = RHS -> P LHS /\ LHS = RHS.
Proof. intros [? ?]; subst; tauto. Qed.
Ltac adjust_goal_for_reflective := apply adjust_goal_for_reflective.
Ltac unmap_wordToZ_tuple term :=
  lazymatch term with
  | (?x, ?y) => let x' := unmap_wordToZ_tuple x in
                let y' := unmap_wordToZ_tuple y in
                constr:((x', y'))
  | map wordToZ ?x => x
  end.
Ltac zrange_to_reflective_hyps_step :=
  match goal with
  | [ H : @ZRange.is_bounded_by ?option_bit_width ?count ?bounds (Tuple.map wordToZ ?arg) |- _ ]
    => let rT := constr:(Syntax.tuple (Tbase TZ) count) in
       let is_bounded_by' := constr:(@Bounds.is_bounded_by rT) in
       let map' := constr:(@cast_back_flat_const (@Bounds.interp_base_type) rT (fun _ => Bounds.bounds_to_base_type) bounds) in
       (* we use [cut] and [abstract] rather than [change] to catch inefficiencies in conversion early, rather than allowing [Defined] to take forever *)
       let H' := fresh H in
       rename H into H';
       assert (H : is_bounded_by' bounds (map' arg)) by (clear -H'; abstract exact H');
       clear H'; move H at top
  end.
Ltac zrange_to_reflective_hyps := repeat zrange_to_reflective_hyps_step.
Ltac zrange_to_reflective_goal :=
  lazymatch goal with
  | [ |- @ZRange.is_bounded_by ?option_bit_width ?count ?bounds (Tuple.map wordToZ ?reified_f_evar)
         /\ Tuple.map wordToZ ?reified_f_evar = ?f ?Zargs ]
    => let T := type of f in
       let f_domain := lazymatch T with ?A -> ?B => A end in
       let T := (eval compute in T) in
       let rT := reify_type T in
       let is_bounded_by' := constr:(@Bounds.is_bounded_by (codomain rT)) in
       let input_bounds := const_tuple f_domain bounds in
       let map_t := constr:(fun t bs => @cast_back_flat_const (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) bs) in
       let map_output := constr:(map_t (codomain rT) bounds) in
       let map_input := constr:(map_t (domain rT) input_bounds) in
       let args := unmap_wordToZ_tuple Zargs in
       (* we use [cut] and [abstract] rather than [change] to catch inefficiencies in conversion early, rather than allowing [Defined] to take forever *)
       cut (is_bounded_by' bounds (map_output reified_f_evar) /\ map_output reified_f_evar = f (map_input args));
       [ generalize reified_f_evar; clear; clearbody f; let x := fresh in intros ? x; abstract exact x
       | ];
       cbv beta
  end;
  adjust_goal_for_reflective.
Ltac zrange_to_reflective := zrange_to_reflective_hyps; zrange_to_reflective_goal.

(** The tactic [refine_to_reflective_glue] is the public-facing one. *)
Ltac refine_to_reflective_glue :=
  do_curry;
  split_BoundedWordToZ;
  zrange_to_reflective.
