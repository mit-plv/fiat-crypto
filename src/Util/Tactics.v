(** * Generic Tactics *)
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.Tactics.BreakMatch.
Require Export Crypto.Util.Tactics.Head.
Require Export Crypto.Util.Tactics.DestructHyps.
Require Export Crypto.Util.Tactics.DestructHead.
Require Export Crypto.Util.Tactics.DoWithHyp.
Require Export Crypto.Util.Tactics.RewriteHyp.
Require Export Crypto.Util.Tactics.SpecializeBy.
Require Export Crypto.Util.Tactics.SplitInContext.
Require Export Crypto.Util.Tactics.UniquePose.
Require Export Crypto.Util.Tactics.VM.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail 0 tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

Ltac get_goal :=
  match goal with |- ?G => G end.

(** [contains x expr] succeeds iff [x] appears in [expr] *)
Ltac contains search_for in_term :=
  idtac;
  lazymatch in_term with
  | appcontext[search_for] => idtac
  end.

Ltac debuglevel := constr:(0%nat).

Ltac solve_debugfail tac :=
  solve [tac] ||
        let dbg := debuglevel in
        match dbg with
        | O => idtac
        | _ => match goal with |- ?G => idtac "couldn't prove" G end
        end.

Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?E] ] => is_evar E; let e := fresh "e" in set (e := E)
         end.

Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.

Ltac subst_let := repeat match goal with | x := _ |- _ => subst x end.

Ltac free_in x y :=
  idtac;
  match y with
    | appcontext[x] => fail 1 x "appears in" y
    | _ => idtac
  end.

Ltac setoid_subst'' R x :=
  is_var x;
  match goal with
  | [ H : R x ?y |- _ ]
    => free_in x y; rewrite ?H in *; clear x H
  | [ H : R ?y x |- _ ]
    => free_in x y; rewrite <- ?H in *; clear x H
  end.

Ltac setoid_subst' x :=
  is_var x;
  match goal with
  | [ H : ?R x _ |- _ ] => setoid_subst'' R x
  | [ H : ?R _ x |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel' R :=
  idtac;
  match goal with
  | [ H : R ?x _ |- _ ] => setoid_subst'' R x
  | [ H : R _ ?x |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel R := repeat setoid_subst_rel' R.

Ltac setoid_subst_all :=
  repeat match goal with
         | [ H : ?R ?x ?y |- _ ] => is_var x; setoid_subst'' R x
         | [ H : ?R ?x ?y |- _ ] => is_var y; setoid_subst'' R y
         end.

Tactic Notation "setoid_subst" ident(x) := setoid_subst' x.
Tactic Notation "setoid_subst" := setoid_subst_all.

Ltac destruct_trivial_step :=
  match goal with
  | [ H : unit |- _ ] => clear H || destruct H
  | [ H : True |- _ ] => clear H || destruct H
  end.
Ltac destruct_trivial := repeat destruct_trivial_step.

Ltac clear_duplicates_step :=
  match goal with
  | [ H : ?T, H' : ?T |- _ ] => clear H'
  | [ H := ?T, H' := ?T |- _ ] => clear H'
  end.
Ltac clear_duplicates := repeat clear_duplicates_step.


(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac do_one_match_then matcher do_tac tac :=
  idtac;
  match goal with
  | [ H : ?T |- _ ]
    => matcher T; do_tac H;
       try match type of H with
           | T => clear H
           end;
       tac
  end.

Ltac do_all_matches_then matcher do_tac tac :=
  repeat do_one_match_then matcher do_tac tac.

Ltac destruct_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => destruct H) tac.
Ltac destruct_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => destruct H) tac.

Ltac inversion_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => inversion H; subst) tac.
Ltac inversion_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => inversion H; subst) tac.

Ltac destruct_all_matches matcher :=
  destruct_all_matches_then matcher ltac:( simpl in * ).
Ltac destruct_one_match matcher := destruct_one_match_then matcher ltac:( simpl in * ).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

Ltac inversion_all_matches matcher := inversion_all_matches_then matcher ltac:( simpl in * ).
Ltac inversion_one_match matcher := inversion_one_match_then matcher ltac:( simpl in * ).
Ltac inversion_all_matches' matcher := inversion_all_matches_then matcher idtac.

(** If [tac_in H] operates in [H] and leaves side-conditions before
    the original goal, then
    [side_conditions_before_to_side_conditions_after tac_in H] does
    the same thing to [H], but leaves side-conditions after the
    original goal. *)
Ltac side_conditions_before_to_side_conditions_after tac_in H :=
  let HT := type of H in
  let HTT := type of HT in
  let H' := fresh in
  rename H into H';
  let HT' := fresh in
  evar (HT' : HTT);
  cut HT';
  [ subst HT'; intro H
  | tac_in H';
    [ ..
    | subst HT'; eexact H' ] ];
  instantiate; (* required in 8.4 for the [move] to succeed, because evar dependencies *)
  [ (* We preserve the order of the hypotheses.  We need to do this
       here, after evars are instantiated, and not above. *)
    move H after H'; clear H'
  | .. ].

(** Execute [progress tac] on all subterms of the goal.  Useful for things like [ring_simplify]. *)
Ltac tac_on_subterms tac :=
  repeat match goal with
         | [ |- context[?t] ]
           => progress tac t
         end.

(** Like [Coq.Program.Tactics.revert_last], but only for non-dependent hypotheses *)
Ltac revert_last_nondep :=
  match goal with
  | [ H : _ |- _ ]
    => lazymatch goal with
       | [ H' : appcontext[H] |- _ ] => fail
       | [ |- appcontext[H] ] => fail
       | _ => idtac
       end;
       revert H
  end.

Ltac reverse_nondep := repeat revert_last_nondep.

Ltac simplify_repeated_ifs_step :=
  match goal with
  | [ |- context G[if ?b then ?x else ?y] ]
    => let x' := match x with
                 | context x'[b] => let x'' := context x'[true] in x''
                 end in
       let G' := context G[if b then x' else y] in
       cut G'; [ destruct b; exact (fun z => z) | cbv iota ]
  | [ |- context G[if ?b then ?x else ?y] ]
    => let y' := match y with
                 | context y'[b] => let y'' := context y'[false] in y''
                 end in
       let G' := context G[if b then x else y'] in
       cut G'; [ destruct b; exact (fun z => z) | cbv iota ]
  end.
Ltac simplify_repeated_ifs := repeat simplify_repeated_ifs_step.

(** Like [specialize] but allows holes that get filled with evars. *)
Tactic Notation "especialize" open_constr(H) := specialize H.

(** [forward H] specializes non-dependent binders in a hypothesis [H]
    with side-conditions.  Side-conditions come after the main goal,
    like with [replace] and [rewrite].

    [eforward H] is like [forward H], but also specializes dependent
    binders with evars.

    Both tactics do nothing on hypotheses they cannot handle. *)
Ltac forward_step H :=
  match type of H with
  | ?A -> ?B => let a := fresh in cut A; [ intro a; specialize (H a); clear a | ]
  end.
Ltac eforward_step H :=
  match type of H with
  | _ => forward_step H
  | forall x : ?A, _
    => let x_or_fresh := fresh x in
       evar (x_or_fresh : A);
       specialize (H x_or_fresh); subst x_or_fresh
  end.
Ltac forward H := try (forward_step H; [ forward H | .. ]).
Ltac eforward H := try (eforward_step H; [ eforward H | .. ]).

(** [simplify_projections] reduces terms of the form [fst (_, _)] (for
    any projection from [prod], [sig], [sigT], or [and]) *)
Ltac pre_simplify_projection proj proj' uproj' :=
  pose proj as proj';
  pose proj as uproj';
  unfold proj in uproj';
  change proj with proj'.
Ltac do_simplify_projection_2Targ_4carg_step proj proj' uproj' construct :=
  change proj' with uproj' at 1;
  lazymatch goal with
  | [ |- appcontext[uproj' _ _ (construct _ _ _ _)] ]
    => cbv beta iota delta [uproj']
  | _ => change uproj' with proj
  end.
Ltac do_simplify_projection_2Targ_4carg proj proj' uproj' construct :=
  repeat do_simplify_projection_2Targ_4carg_step proj proj' uproj' construct.
Ltac simplify_projection_2Targ_4carg proj construct :=
  let proj' := fresh "proj" in
  let uproj' := fresh "proj" in
  pre_simplify_projection proj proj' uproj';
  do_simplify_projection_2Targ_4carg proj proj' uproj' construct;
  clear proj' uproj'.

Ltac simplify_projections :=
  repeat (simplify_projection_2Targ_4carg @fst @pair
          || simplify_projection_2Targ_4carg @snd @pair
          || simplify_projection_2Targ_4carg @proj1_sig @exist
          || simplify_projection_2Targ_4carg @proj2_sig @exist
          || simplify_projection_2Targ_4carg @projT1 @existT
          || simplify_projection_2Targ_4carg @projT2 @existT
          || simplify_projection_2Targ_4carg @proj1 @conj
          || simplify_projection_2Targ_4carg @proj2 @conj).

(** constr-based [idtac] *)
Class cidtac {T} (msg : T) := Build_cidtac : True.
Hint Extern 0 (cidtac ?msg) => idtac msg; exact I : typeclass_instances.
(** constr-based [idtac] *)
Class cidtac2 {T1 T2} (msg1 : T1) (msg2 : T2) := Build_cidtac2 : True.
Hint Extern 0 (cidtac2 ?msg1 ?msg2) => idtac msg1 msg2; exact I : typeclass_instances.
Class cidtac3 {T1 T2 T3} (msg1 : T1) (msg2 : T2) (msg3 : T3) := Build_cidtac3 : True.
Hint Extern 0 (cidtac3 ?msg1 ?msg2 ?msg3) => idtac msg1 msg2 msg3; exact I : typeclass_instances.

Class cfail {T} (msg : T) := Build_cfail : True.
Hint Extern 0 (cfail ?msg) => idtac "Error:" msg; exact I : typeclass_instances.
Class cfail2 {T1 T2} (msg1 : T1) (msg2 : T2) := Build_cfail2 : True.
Hint Extern 0 (cfail2 ?msg1 ?msg2) => idtac "Error:" msg1 msg2; exact I : typeclass_instances.
Class cfail3 {T1 T2 T3} (msg1 : T1) (msg2 : T2) (msg3 : T3) := Build_cfail3 : True.
Hint Extern 0 (cfail3 ?msg1 ?msg2 ?msg3) => idtac "Error:" msg1 msg2 msg3; exact I : typeclass_instances.

Ltac cidtac msg := constr:(_ : cidtac msg).
Ltac cidtac2 msg1 msg2 := constr:(_ : cidtac2 msg1 msg2).
Ltac cidtac3 msg1 msg2 msg3 := constr:(_ : cidtac2 msg1 msg2 msg3).
Ltac cfail msg := let dummy := constr:(_ : cfail msg) in constr:(I : I).
Ltac cfail2 msg1 msg2 := let dummy := constr:(_ : cfail2 msg1 msg2) in constr:(I : I).
Ltac cfail3 msg1 msg2 msg3 := let dummy := constr:(_ : cfail2 msg1 msg2 msg3) in constr:(I : I).

Ltac idtac_goal := lazymatch goal with |- ?G => idtac "Goal:" G end.
Ltac idtac_context :=
  try (repeat match goal with H : _ |- _ => revert H end;
       idtac_goal;
       lazymatch goal with |- ?G => idtac "Context:" G end;
       fail).

(** Destruct the convoy pattern ([match e as x return x = e -> _ with _ => _ end eq_refl] *)
Ltac convoy_destruct_gen T change_in :=
  let e' := fresh in
  let H' := fresh in
  match T with
  | context G[?f eq_refl]
    => match f with
       | match ?e with _ => _ end
         => pose e as e';
            match f with
            | context F[e]
              => let F' := context F[e'] in
                 first [ pose (eq_refl : e = e') as H';
                         let G' := context G[F' H'] in
                         change_in G';
                         clearbody H' e'
                       | pose (eq_refl : e' = e) as H';
                         let G' := context G[F' H'] in
                         change_in G';
                         clearbody H' e' ]
            end
       end;
       destruct e'
  end.

Ltac convoy_destruct_in H :=
  let T := type of H in
  convoy_destruct_gen T ltac:(fun T' => change T' in H).
Ltac convoy_destruct :=
  let T := get_goal in
  convoy_destruct_gen T ltac:(fun T' => change T').
