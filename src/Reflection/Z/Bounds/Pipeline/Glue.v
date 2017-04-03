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
Require Import Crypto.Util.Sigma.Associativity.
Require Import Crypto.Util.Tactics.EvarExists.

Module Export Exports.
  Export Crypto.Reflection.Z.Reify. (* export for the tactic redefinitions *)
End Exports.

(** The [reassoc_sig_and_eexists] tactic operates on a goal convertible with
<<
{ f : { a | is_bounded_by bounds a }
| BoundedWordToZ f = rexprZ (BoundedWordToZ a) ... (BoundedWordToZ z) }
>>
    and leaves a goal of the form
<<
is_bounded_by bounds (map wordToZ ?f)
  /\ map wordToZ ?f = rexprZ (map wordToZ (proj1_sig a)) ... (map wordToZ (proj1_sig z))
>>
    where [?f] is a context variable set to a new evar.  This tactic
    relies on the exact definition of [BoundedWordToZ]. *)
Ltac reassoc_sig_and_eexists :=
  cbv [BoundedWordToZ];
  sig_sig_assoc;
  evar_exists.

(** The [do_curry] tactic takes a goal of the form
<<
_ /\ BoundedWordToZ (?f a b ... z) = F A B ... Z
>>
    and turns it into a goal of the form
<<
_ /\ BoundedWordToZ (f' (a, b, ..., z)) = F' (A, B, ..., Z)
>>

    Note that the number of arguments on the left and on the right DO
    NOT need to be the same.  *)
Ltac do_curry :=
  lazymatch goal with
  | [ |- _ /\ ?BWtoZ ?f_bw = ?f_Z ]
    => let f_bw := head f_bw in
       let f_Z := head f_Z in
       change_with_curried f_Z;
       change_with_curried f_bw
  end.

(** The [split_BoundedWordToZ] tactic takes a goal of the form
<<
_ /\ map wordToZ (proj1_sig f) = F ARGS
>>
    and splits [f] and any arguments in ARGS into two parts, part
    about the computational behavior, and another part about the
    boundedness.

    This pipeline relies on the specific definition of [BoundedWordToZ],
    and requires [f] to be a context variable which is set to a single
    evar. *)
Ltac check_precondition _ :=
  lazymatch goal with
  | [ |- @ZRange.is_bounded_by ?option_bit_width ?count ?bounds (map wordToZ ?f)
         /\ map wordToZ ?f = _ ]
    => first [ is_var f | fail 1 "The argument to BoundedWordToZ must be a bare context-definition set to an evar, not"
                               f "which is not a variable" ];
       match goal with
       | [ f' := ?f_evar |- _ ]
         => constr_eq f f';
            first [ is_evar f_evar | fail 2 "The argument to BoundedWordToZ must be a context-definition set to an evar, not"
                                          f' "which is defined as" f_evar ]
       | [ f' : _ |- _ ]
         => constr_eq f f';
            fail 1 "The argument to BoundedWordToZ must be a context-definition set to an evar, not"
                 f' "which has no body"
       | _ => fail 1 "The argument to BoundedWordToZ must be a context-definition, not" f "which does not appear in the context"
       end
  | [ |- ?G ]
    => let expected := uconstr:(@ZRange.is_bounded_by _ _ _ (map wordToZ ?[f])
                                /\ map wordToZ ?[f] = _) in
       fail "The post-processed goal should have the form"
            expected
            "not"
            G
  end.
Ltac split_BoundedWordToZ :=
  (** first revert the context definition which is an evar named [f]
      in the docs above, so that it becomes evar 1 (for
      [instantiate]), and so that [make_evar_for_first_projection]
      works *)
  check_precondition ();
  lazymatch goal with
  | [ |- _ /\ map wordToZ ?f = _ ]
    => revert f
  end;
  repeat match goal with
         | [ |- context[map wordToZ (proj1_sig ?x)] ]
           => is_var x;
              first [ clearbody x; fail 1
                    | (** we want to keep the same context variable in
                          the evar that we reverted above, and in the
                          current goal; hence the instantiate trick *)
                    instantiate (1:=ltac:(destruct x)); destruct x ]
         end;
  cbv beta iota; intro; (* put [f] back in the context so that [cbn] doesn't remove this let-in *)
  cbn [proj1_sig].

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
       (* we use [assert] and [abstract] rather than [change] to catch
          inefficiencies in conversion early, rather than allowing
          [Defined] to take forever *)
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
       (* we use [cut] and [abstract] rather than [change] to catch
          inefficiencies in conversion early, rather than allowing
          [Defined] to take forever *)
       cut (is_bounded_by' bounds (map_output reified_f_evar) /\ map_output reified_f_evar = f (map_input args));
       [ generalize reified_f_evar; clear; clearbody f; clear; let x := fresh in intros ? x; abstract exact x
       | ];
       cbv beta
  end;
  adjust_goal_for_reflective.
Ltac zrange_to_reflective := zrange_to_reflective_hyps; zrange_to_reflective_goal.

(** The tactic [refine_to_reflective_glue] is the public-facing one;
    it takes a goal of the form
<<
BoundedWordToZ ?f = F (BoundedWordToZ A) (BoundedWordToZ B) ... (BoundedWordToZ Z)
>>
    where [?f] is an evar, and turns it into a goal the that
    reflective automation pipeline can handle. *)
Ltac refine_to_reflective_glue :=
  reassoc_sig_and_eexists;
  do_curry;
  split_BoundedWordToZ;
  zrange_to_reflective_goal.
