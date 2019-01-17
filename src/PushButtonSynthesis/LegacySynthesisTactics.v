(** * Push-Button Synthesis: Legacy Synthesis Tactics *)
Require Import Coq.Classes.Morphisms.
Require Import Crypto.LanguageWf.
Require Import Crypto.Language.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.Util.Equality. (* fg_equal_rel *)
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.GetGoal.

Import
  LanguageWf.Compilers
  Language.Compilers.
Import Compilers.defaults.

(** TODO: Port Barrett and Montgomery to the new glue style, and remove these tactics.  These tactics are only needed for the old-glue-style derivations. *)
Ltac peel_interp_app _ :=
  lazymatch goal with
  | [ |- ?R' (?InterpE ?arg) (?f ?arg) ]
    => apply fg_equal_rel; [ | reflexivity ];
       try peel_interp_app ()
  | [ |- ?R' (Interp ?ev) (?f ?x) ]
    => let sv := type of x in
       let fx := constr:(f x) in
       let dv := type of fx in
       let rs := reify_type sv in
       let rd := reify_type dv in
       etransitivity;
       [ apply @expr.Interp_APP_rel_reflexive with (s:=rs) (d:=rd) (R:=R');
         typeclasses eauto
       | apply fg_equal_rel;
         [ try peel_interp_app ()
         | try lazymatch goal with
               | [ |- ?R (Interp ?ev) (Interp _) ]
                 => reflexivity
               | [ |- ?R (Interp ?ev) ?c ]
                 => let rc := constr:(GallinaReify.Reify c) in
                    unify ev rc; vm_compute; reflexivity
               end ] ]
  end.
Ltac pre_cache_reify _ :=
  let H' := fresh in
  lazymatch goal with
  | [ |- ?P /\ Wf ?e ]
    => let P' := fresh in
       evar (P' : Prop);
       assert (H' : P' /\ Wf e); subst P'
  end;
  [
      | split; [ destruct H' as [H' _] | destruct H' as [_ H']; exact H' ];
        cbv [type.app_curried];
        let arg := fresh "arg" in
        let arg2 := fresh in
        intros arg arg2;
        cbn [type.and_for_each_lhs_of_arrow type.eqv];
        let H := fresh in
        intro H;
        repeat match type of H with
               | and _ _ => let H' := fresh in
                            destruct H as [H' H];
                            rewrite <- H'
               end;
        clear dependent arg2; clear H;
        intros _;
        peel_interp_app ();
        [ lazymatch goal with
          | [ |- ?R (Interp ?ev) _ ]
            => (tryif is_evar ev
                 then let ev' := fresh "ev" in set (ev' := ev)
                 else idtac)
          end;
          cbv [pointwise_relation];
          repeat lazymatch goal with
                 | [ H : _ |- _ ] => first [ constr_eq H H'; fail 1
                                           | revert H ]
                 end;
          eexact H'
        | .. ] ];
  [ intros; clear | .. ].
Ltac do_inline_cache_reify do_if_not_cached :=
  pre_cache_reify ();
  [ try solve [
          cbv beta zeta;
          repeat match goal with H := ?e |- _ => is_evar e; subst H end;
          try solve [ split; [ solve [ eauto with nocore reify_gen_cache ] | solve [ eauto with wf_gen_cache; prove_Wf () ] ] ];
          do_if_not_cached ()
        ];
    cache_reify ()
  | .. ].

(* TODO: MOVE ME *)
Ltac vm_compute_lhs_reflexivity :=
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let x := (eval vm_compute in LHS) in
       (* we cannot use the unify tactic, which just gives "not
          unifiable" as the error message, because we want to see the
          terms that were not unifable.  See also
          COQBUG(https://github.com/coq/coq/issues/7291) *)
       let _unify := constr:(ltac:(reflexivity) : RHS = x) in
       vm_cast_no_check (eq_refl x)
  end.

Ltac solve_rop' rop_correct do_if_not_cached machine_wordsizev :=
  eapply rop_correct with (machine_wordsize:=machine_wordsizev);
  [ do_inline_cache_reify do_if_not_cached
  | subst_evars; vm_compute_lhs_reflexivity (* lazy; reflexivity *) ].
Ltac solve_rop_nocache rop_correct :=
  solve_rop' rop_correct ltac:(fun _ => idtac).
Ltac solve_rop rop_correct :=
  solve_rop'
    rop_correct
    ltac:(fun _ => let G := get_goal in fail 2 "Could not find a solution in reify_gen_cache for" G).
