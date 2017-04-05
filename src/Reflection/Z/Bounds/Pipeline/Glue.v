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
Require Import Crypto.Util.Sigma.MapProjections.
Require Import Crypto.Util.Tactics.EvarExists.
Require Import Crypto.Util.Tactics.GetGoal.
Require Import Crypto.Util.Tactics.PrintContext.
Require Import Crypto.Util.Tactics.MoveLetIn.

Module Export Exports.
  Export Crypto.Reflection.Z.Reify. (* export for the tactic redefinitions *)
End Exports.

(** ** [reassoc_sig_and_eexists] *)
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


(** The tactic [unfold_paired_tuple_map] unfolds any [Tuple.map]s
    applied to [pair]s. *)
Ltac unfold_paired_tuple_map :=
  repeat match goal with
         | [ |- context[Tuple.map (n:=S ?N) _ (pair _ _)] ]
           => progress change (@Tuple.map (S N)) with (fun A B f => @Tuple.map' A B f N); cbv beta iota delta [Tuple.map']
         end.
(** The tactic [preunfold_and_dlet_to_context] will unfold
    [BoundedWordToZ] and [Tuple.map]s applied to [pair]s, and then
    look for a [dlet x := y in ...] in the RHS of a goal of shape [{a
    | LHS = RHS }] and replace it with a context variable. *)
Ltac preunfold_and_dlet_to_context :=
  unfold_paired_tuple_map;
  cbv [BoundedWordToZ]; cbn [fst snd proj1_sig];
  sig_dlet_in_rhs_to_context.
(** The tactic [pattern_proj1_sig_in_lhs_of_sig] takes a goal of the form
<<
{ a : A | P }
>>
    where [A] is a sigma type, and leaves a goal of the form
<<
{ a : A | dlet p := P' in p (proj1_sig a)
>>
    where all occurrences of [proj1_sig a] have been abstracted out of
    [P] to make [P']. *)
Ltac pattern_proj1_sig_in_sig :=
  eapply proj2_sig_map;
  [ let a := fresh in
    let H := fresh in
    intros a H; pattern (proj1_sig a);
    lazymatch goal with
    | [ |- ?P ?p1a ]
      => cut (dlet p := P in p p1a);
         [ clear; abstract (cbv [Let_In]; exact (fun x => x)) | ]
    end;
    exact H
  | cbv beta ].
(** The tactic [pattern_sig_sig_assoc] takes a goal of the form
<<
{ a : { a' : A | P } | Q }
>>
    where [Q] mentions [proj1_sig a] but not [proj2_sig a], and leaves
    a goal of the form
<<
{ a : A | P /\ Q }
>>
 *)
Ltac pattern_sig_sig_assoc :=
  pattern_proj1_sig_in_sig;
  let f := fresh in
  goal_dlet_to_context_step f;
  apply sig_sig_assoc;
  subst f; cbv beta.
(** The tactic [reassoc_sig_and_eexists] will unfold [BoundedWordToZ]
    and move any [dlet x := ... in ...] to context variables, and then
    take a goal of the form
<<
{ a : { a' : A | P a' } | Q (proj1_sig a) }
>>
    where [Q] mentions [proj1_sig a] but not [proj2_sig a], and leave
    a goal of the form
<<
P ?a /\ Q ?a
>>
 *)
Ltac reassoc_sig_and_eexists :=
  preunfold_and_dlet_to_context;
  pattern_sig_sig_assoc;
  evar_exists.

(** ** [do_curry_rhs] *)
(** The [do_curry_rhs] tactic takes a goal of the form
<<
_ /\ _ = F A B ... Z
>>
    and turns it into a goal of the form
<<
_ /\ _ = F' (A, B, ..., Z)
>>
 *)
Ltac do_curry_rhs :=
  lazymatch goal with
  | [ |- _ /\ _ = ?f_Z ]
    => let f_Z := head f_Z in
       change_with_curried f_Z
  end.

(** ** [split_BoundedWordToZ] *)
(** The [split_BoundedWordToZ] tactic takes a goal of the form
<<
_ /\ (map wordToZ (proj1_sig f1), ... map wordToZ (proj1_sig fn)) = F ARGS
>>
    and splits [f1] ... [fn] and any arguments in ARGS into two
    parts, one part about the computational behavior, and another part
    about the boundedness.

    This pipeline relies on the specific definition of
    [BoundedWordToZ], and requires [f] to be a context variable which
    is set to a single evar. *)
(** First we ensure the goal has the right shape, and give helpful
    error messages if it does not *)
Ltac check_fW_type descr top_fW fW :=
  lazymatch fW with
  | fst ?fW => check_fW_type descr top_fW fW
  | snd ?fW => check_fW_type descr top_fW fW
  | _ => let G := get_goal in
         let shape := uconstr:(map wordToZ ?fW) in
         let efW := uconstr:(?fW) in
         first [ is_var fW
               | fail 1 "In the goal" G
                      descr shape
                      "where" efW "must be a repeated application of fst and snd"
                      "to a single context variable which is defined to be an evar."
                      "The term" top_fW "is based on" fW "which is not a variable" ];
         match goal with
         | [ fW' := ?e |- _ ]
           => constr_eq fW' fW;
              first [ is_evar e
                    | fail 2 "In the goal" G
                           descr shape
                           "where" efW "must be a repeated application of fst and snd"
                           "to a single context variable which is defined to be an evar."
                           "The term" top_fW "is based on" fW' "which is a context variable"
                           "with body" e "which is not a bare evar" ]
         | [ fW' : _ |- _ ]
           => constr_eq fW fW';
              fail 1 "In the goal" G
                   descr shape
                   "where" efW "must be a repeated application of fst and snd"
                   "to a single context variable which is defined to be an evar."
                   "The term" top_fW "is based on" fW' "which is a context variable without a body"
         | _ => fail 1 "In the goal" G
                     descr shape
                     "where" efW "must be a repeated application of fst and snd"
                     "to a single context variable which is defined to be an evar."
                     "The term" top_fW "is based on" fW "which is not a context variable"
         end
  end.
Tactic Notation "check_fW_type" string(descr) constr(fW)
  := check_fW_type descr fW fW.
Ltac check_is_bounded_by_shape subterm_type :=
  lazymatch subterm_type with
  | ZRange.is_bounded_by None ?bounds (map wordToZ ?fW)
    => check_fW_type "The ℤ argument to is_bounded_by must have the shape" fW
  | ?A /\ ?B
    => check_is_bounded_by_shape A;
       check_is_bounded_by_shape B
  | _ => let G := get_goal in
         let shape := uconstr:(ZRange.is_bounded_by None ?bounds (map wordToZ ?fW)) in
         fail "In the goal" G
              "The first conjunct of the goal is expected to be a conjunction of things of the shape" shape
              "but a subterm not matching this shape was found:" subterm_type
  end.
Ltac check_LHS_Z_shape subterm :=
  lazymatch subterm with
  | map wordToZ ?fW
    => check_fW_type "The left-hand side of the second conjunct of the goal must be a tuple of terms with shape" fW
  | (?A, ?B)
    => check_LHS_Z_shape A;
       check_LHS_Z_shape B
  | _ => let G := get_goal in
         let shape := uconstr:(map wordToZ ?fW) in
         fail "In the goal" G
              "The second conjunct of the goal is expected to be a equality whose"
              "left-hand side is a tuple of terms of the shape" shape
              "but a subterm not matching this shape was found:" subterm
  end.
Ltac check_RHS_Z_shape_rec subterm :=
  lazymatch subterm with
  | map wordToZ ?fW
    => idtac
  | (?A, ?B)
    => check_RHS_Z_shape_rec A;
       check_RHS_Z_shape_rec B
  | _ => let G := get_goal in
         let shape := uconstr:(map wordToZ ?fW) in
         fail "In the goal" G
              "The second conjunct of the goal is expected to be a equality whose"
              "right-hand side is the application of a function to a tuple of terms of the shape" shape
              "but a subterm not matching this shape was found:" subterm
  end.
Ltac check_RHS_Z_shape RHS :=
  lazymatch RHS with
  | ?f ?args
    => check_RHS_Z_shape_rec args
  | _ => let G := get_goal in
         let shape := uconstr:(map wordToZ ?fW) in
         fail "In the goal" G
              "The second conjunct of the goal is expected to be a equality whose"
              "right-hand side is the application of a function to a tuple of terms of the shape" shape
              "but the right-hand side is not a function application:" RHS
  end.
Ltac check_precondition _ :=
  lazymatch goal with
  | [ |- ?is_bounded_by /\ ?LHS = ?RHS ]
    => check_is_bounded_by_shape is_bounded_by;
       check_LHS_Z_shape LHS;
       check_RHS_Z_shape RHS
  | [ |- ?G ]
    => let shape := uconstr:(?is_bounded /\ ?LHS = ?RHS) in
       fail "The goal has the wrong shape for reflective gluing; expected" shape "but found" G
  end.
Ltac split_BoundedWordToZ :=
  (** first revert the context definition which is an evar named [f]
      in the docs above, so that it becomes evar 1 (for
      [instantiate]), and so that [make_evar_for_first_projection]
      works.  It's not the most robust way to find the right term;
      maybe we should modify some of the checks above to assert that
      the evar found is a particular one? *)
  check_precondition ();
  lazymatch goal with
  | [ |- _ /\ ?LHS = _ ]
    => match goal with
       | [ f := ?e |- _ ]
         => is_evar e; match LHS with context[f] => idtac end;
            revert f
       end
  end;
  repeat match goal with
         | [ |- context[map wordToZ (proj1_sig ?x)] ]
           => is_var x;
              first [ clearbody x; fail 1
                    | (** we want to keep the same context variable in
                          the evar that we reverted above, and in the
                          current goal; hence the instantiate trick *)
                    instantiate (1:=ltac:(destruct x)); destruct x ]
         | [ |- context[fst ?x] ]
           => is_var x;
              first [ clearbody x; fail 1
                    | (** we want to keep the same context variable in
                          the evar that we reverted above, and in the
                          current goal; hence the instantiate trick *)
                    change (fst x) with (let (a, b) := x in a);
                    change (snd x) with (let (a, b) := x in b);
                    instantiate (1:=ltac:(destruct x)); destruct x ];
              cbv beta iota
         end;
  cbv beta iota; intro; (* put [f] back in the context so that [cbn] doesn't remove this let-in *)
  cbn [proj1_sig].

(** ** [zrange_to_reflective] *)
(** The [zrange_to_reflective] tactic takes a goal of the form
<<
(is_bounded_by _ bounds (map wordToZ (?fW args)) /\ ...)
  /\ (map wordToZ (?fW args), ...) = fZ argsZ
>>
    and uses [cut] and a small lemma to turn it into a goal that the
    reflective machinery can handle.  The goal left by this tactic
    should be fully solvable by the reflective pipeline. *)

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
Ltac bounds_from_is_bounded_by T :=
  lazymatch T with
  | ?A /\ ?B => let a := bounds_from_is_bounded_by A in
                let b := bounds_from_is_bounded_by B in
                constr:((a, b))
  | ZRange.is_bounded_by _ ?bounds _
    => bounds
  end.
Ltac pose_proof_bounded_from_Zargs_hyps Zargs H :=
  lazymatch Zargs with
  | (?a, ?b)
    => let Ha := fresh in
       let Hb := fresh in
       pose_proof_bounded_from_Zargs_hyps a Ha;
       pose_proof_bounded_from_Zargs_hyps b Hb;
       let pf := constr:(conj Ha Hb) in
       lazymatch type of pf with
       | @Bounds.is_bounded_by ?A ?boundsA (@cast_back_flat_const ?var ?tA ?f ?VA ?argsA)
         /\ @Bounds.is_bounded_by ?B ?boundsB (@cast_back_flat_const ?var ?tB ?f ?VB ?argsB)
         => pose proof
                 ((pf : @Bounds.is_bounded_by
                          (Prod A B) (boundsA, boundsB)
                          (@cast_back_flat_const var (Prod tA tB) f (VA, VB) (argsA, argsB))))
           as H;
            clear Ha Hb
       | ?pfT
         => let shape
                := uconstr:(@Bounds.is_bounded_by ?A ?boundsA (@cast_back_flat_const ?var ?tA ?f ?VA ?argsA)
                            /\ @Bounds.is_bounded_by ?B ?boundsB (@cast_back_flat_const ?var ?tB ?f ?VB ?argsB)) in
            fail 1 "Returned value from recursive call of bounded_from_Zargs_hyps has the wrong type"
                 "Cannot match type" pfT
                 "with shape" shape
       end
  | Tuple.map wordToZ ?arg
    => lazymatch goal with
       | [ H' : Bounds.is_bounded_by ?bounds (cast_back_flat_const arg) |- _ ]
         => rename H' into H
       | _ => let shape := uconstr:(Bounds.is_bounded_by _ (cast_back_flat_const arg)) in
              idtac "In the context:"; print_context ();
              fail 1 "Could not find bounds in the context for" arg
                   "when looking for a hypothesis of shape" shape
       end
  end.
Ltac find_reified_f_evar LHS :=
  lazymatch LHS with
  | fst ?x => find_reified_f_evar x
  | snd ?x => find_reified_f_evar x
  | (?x, _) => find_reified_f_evar x
  | map wordToZ ?x => find_reified_f_evar x
  | _ => LHS
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
Ltac zrange_to_reflective_goal Hbounded :=
  lazymatch goal with
  | [ |- ?is_bounded_by_T /\ ?LHS = ?f ?Zargs ]
    => let T := type of f in
       let f_domain := lazymatch T with ?A -> ?B => A end in
       let T := (eval compute in T) in
       let rT := reify_type T in
       let is_bounded_by' := constr:(@Bounds.is_bounded_by (codomain rT)) in
       let output_bounds := bounds_from_is_bounded_by is_bounded_by_T in
       pose_proof_bounded_from_Zargs_hyps Zargs Hbounded;
       let input_bounds := lazymatch type of Hbounded with Bounds.is_bounded_by ?bounds _ => bounds end in
       let map_t := constr:(fun t bs => @cast_back_flat_const (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) bs) in
       let map_output := constr:(map_t (codomain rT) output_bounds) in
       let map_input := constr:(map_t (domain rT) input_bounds) in
       let args := unmap_wordToZ_tuple Zargs in
       let reified_f_evar := find_reified_f_evar LHS in
       (* we use [cut] and [abstract] rather than [change] to catch
          inefficiencies in conversion early, rather than allowing
          [Defined] to take forever *)
       cut (is_bounded_by' output_bounds (map_output reified_f_evar) /\ map_output reified_f_evar = f (map_input args));
       [ generalize reified_f_evar; clear; clearbody f; clear; let x := fresh in intros ? x; abstract exact x
       | ];
       cbv beta
  end;
  adjust_goal_for_reflective.
Ltac zrange_to_reflective Hbounded := zrange_to_reflective_hyps; zrange_to_reflective_goal Hbounded.

(** ** [refine_to_reflective_glue] *)
(** The tactic [refine_to_reflective_glue] is the public-facing one;
    it takes a goal of the form
<<
BoundedWordToZ ?f = F (BoundedWordToZ A) (BoundedWordToZ B) ... (BoundedWordToZ Z)
>>
    where [?f] is an evar, and turns it into a goal the that
    reflective automation pipeline can handle. *)
Ltac refine_to_reflective_glue' Hbounded :=
  reassoc_sig_and_eexists;
  do_curry_rhs;
  split_BoundedWordToZ;
  zrange_to_reflective Hbounded.
Ltac refine_to_reflective_glue :=
  let Hbounded := fresh "Hbounded" in
  refine_to_reflective_glue' Hbounded.
