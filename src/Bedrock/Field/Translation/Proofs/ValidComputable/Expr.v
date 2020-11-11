Require Import Coq.derive.Derive.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Expr.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.UniquePose.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations.
Import Inversion.Compilers.

Section Expr.
  Context {p : Types.parameters} {p_ok : @ok p}.

  Local Existing Instance Types.rep.Z.
  Local Existing Instance Types.rep.listZ_local.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  Ltac intros_do_revert tac :=
    lazymatch goal with
    | [ |- forall x : _, _ ] => let x' := fresh in intro x'; intros_do_revert tac; revert x'
    | _ => tac ()
    end.

  Ltac split_lists :=
    refine (@nth_error_true_fold_left_orb_true _ _ _ _);
    [ > cbn [nth_error];
      repeat lazymatch goal with
             | [ |- nth_error (_ :: _) ?n = Some true ]
               => is_evar n;
                  let n' := open_constr:(S _) in
                  unify n n';
                  cbn [nth_error]
             | [ |- nth_error ?ev ?n = Some true ]
               => let ev := head ev in
                  is_evar ev; is_evar n;
                  let EV := fresh in
                  pose ev as EV;
                  instantiate (1:=ltac:(intros_do_revert ltac:(fun _ => refine (cons _ _)))) in (value of EV); clear EV; cbv beta;
                  unify n O;
                  cbn [nth_error]; apply f_equal
             end .. ].

  Ltac get_last ls :=
    lazymatch ls with
    | cons _ ?ls => get_last ls
    | _ => ls
    end.
  Ltac handle_first_var lhs :=
    lazymatch lhs with
    | ?ev ?x ?y => handle_first_var (ev x)
    | ?ev ?e
      => is_evar ev;
         (tryif is_var e
           then instantiate (1:=ltac:(intro)); cbv beta
           else instantiate (1:=ltac:(let e := fresh "e" in intro e; case e; clear e)); cbv beta iota in * )
    end.
  Ltac split_recr valid_expr_bool :=
    lazymatch goal with
    | [ H : valid_expr_bool _ _ _ = true |- _ ]
      => instantiate (1:=ltac:(let e := fresh "e" in intro e; refine (andb _ _); revert e));
         cbv beta; refine (andb_true_intro _); split;
         [ clear H; split_recr valid_expr_bool | clear -H ]
    | _ => instantiate (1:=fun _ => true); reflexivity
    end.
  Ltac get_first_arg f :=
    lazymatch f with
    | ?f ?x
      => lazymatch f with
         | ?f' _ => get_first_arg f
         | _ => x
         end
    end.
  Ltac terms_intersect x y :=
    match x with
    | context[?x'] => match y with
                      | context[x'] => constr:(true)
                      end
    | _ => constr:(false)
    end.
  Ltac destruct_to_instantiate_with valid_expr_bool H x :=
    repeat lazymatch goal with
           | [ |- ?lhs = true ]
             => let x' := get_first_arg lhs in
                let inter := terms_intersect x x' in
                lazymatch inter with
                | false => instantiate (1:=ltac:(intro)); cbv beta
                | true => handle_first_var lhs
                end
           end;
    (instantiate (1:=ltac:(refine (valid_expr_bool _ _ _); clear valid_expr_bool)));
    refine H.
  Ltac instantiate_non_recr valid_expr_bool :=
    clear dependent valid_expr_bool;
    repeat match goal with
             [ H : valid_expr _ _ |- _ ] => clear H
           end;
    repeat lazymatch goal with
           | [ |- ?lhs = true ]
             => handle_first_var lhs
           end;
    repeat lazymatch goal with
           | [ H : _ |- _ ]
             => lazymatch type of H with
                | _ = true
                  => refine (andb_true_intro _); split;
                     [ clear H
                     | refine H ]
                | ?T
                  => lazymatch type of T with
                     | Prop
                       => refine (andb_true_intro _); split;
                          [ clear H
                          | solve [ refine (unreflect_bool H) ]
                            || (idtac "could not reflect:" T; fail) ]
                     | _ => clear H
                     end
                end
           | _ => instantiate (1:=true); reflexivity
           end.
  Ltac unfold_valid_expr_bool valid_expr_bool :=
    cbv [valid_expr_bool]; fold valid_expr_bool; clearbody valid_expr_bool.
  Ltac finish_non_recr_instantiation valid_expr_bool :=
    instantiate (1:=ltac:(let e := fresh "e" in
                          intro e;
                          refine (andb _ _);
                          [ clear valid_expr_bool
                          | ];
                          revert e));
    cbv beta;
    (refine (andb_true_intro _); split;
     [ instantiate_non_recr valid_expr_bool; shelve
     | split_recr valid_expr_bool ]).
  Ltac finish_recr_instantiation valid_expr_bool :=
    lazymatch goal with
    | [ H : valid_expr_bool _ _ ?x = true |- _ ]
      => destruct_to_instantiate_with valid_expr_bool H x
    end.
  Ltac get_valid_expr_bool :=
    lazymatch reverse goal with
    | [ valid_expr_bool : forall t, bool -> API.expr t -> bool |- _ ]
      => valid_expr_bool
    end.
  Ltac get_valid_expr_bool_correct valid_expr_bool :=
    lazymatch goal with
    | [ valid_expr_bool_correct : forall t rc e, valid_expr_bool t rc e = true -> valid_expr rc e |- _ ] => valid_expr_bool_correct
    end.
  Ltac fill_valid_expr_bool_after_split_lists :=
    unshelve (
        let valid_expr_bool := get_valid_expr_bool in
        finish_non_recr_instantiation valid_expr_bool;
        finish_recr_instantiation valid_expr_bool
      );
    try (intros; exact false).
  Ltac fill_valid_expr_bool :=
    (let valid_expr_bool := get_valid_expr_bool in
     unfold_valid_expr_bool valid_expr_bool);
    split_lists;
    fill_valid_expr_bool_after_split_lists.

  Ltac early_safe_step1 :=
    first [ progress cbn [andb] in *
          | match goal with
            | [ |- false = true -> _ ] => intro
            | [ |- true = false -> _ ] => intro
            | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
            | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
            end ].
  Ltac early_safe_step2 :=
    first [ match goal with
            | [ |- context[match ?e with _ => _ end] ] => is_var e; destruct e
            | [ H : context[match ?e with _ => _ end] |- _ ] => is_var e; destruct e
            | [ veb := _ : bool |- _ ] => clearbody veb
            end ].
  Ltac early_safe_step := first [ early_safe_step1 | early_safe_step2 ].
  Ltac early_step valid_expr_bool valid_expr_bool_correct :=
    first [ early_safe_step1
          | match goal with
            | [ |- context[valid_expr_bool ?t ?rc ?e] ]
              => unique pose proof (valid_expr_bool_correct t rc e);
                 let veb := fresh "veb" in
                 set (veb := valid_expr_bool t rc e) in *
            | [ |- context[?e] ]
              => lazymatch e with
                 | context[valid_expr_bool]
                   => match e with
                      | context[match ?e with _ => _ end] => is_var e; destruct e
                      end
                 end
            end
          | early_safe_step2 ].

  Definition valid_expr_bool_package
    : { valid_expr_bool_step
        : ((forall {t} (rc : bool) (e : API.expr t), bool)
           -> (forall {t} (rc : bool) (e : API.expr t), bool))
          & { valid_expr_bool
              : (forall {t} (rc : bool) (e : API.expr t), bool)
                & (forall {t} (rc : bool) (e : API.expr t),
                  (*reflect (valid_expr rc e) (valid_expr_bool t rc e)*)
                  valid_expr rc e -> valid_expr_bool t rc e = true)
                  * (forall {t} (rc : bool) (e : API.expr t),
                        @valid_expr_bool t rc e = @valid_expr_bool_step (@valid_expr_bool) t rc e) }%type }.
  Proof using Type.
    clear p_ok.
    unshelve
      (simple refine (let valid_expr_bool_step
                          : (forall {t} (rc : bool) (e : API.expr t), bool)
                            -> (forall {t} (rc : bool) (e : API.expr t), bool)
                          := fun valid_expr_bool t rc e
                             => fold_left orb _ false in
                      let valid_expr_bool := (fix valid_expr_bool {t} (rc : bool) (e : API.expr t) {struct e} : bool := valid_expr_bool_step (@valid_expr_bool) t rc e) in
                      let valid_expr_bool_eta : forall t rc e, @valid_expr_bool t rc e = valid_expr_bool_step (@valid_expr_bool) t rc e
                          := _ in
                      (*let valid_expr_bool_step_correct'
                          : (forall (t : API.type) (rc : bool) (e : API.expr t),
                                @valid_expr_bool t rc e = true -> valid_expr rc e)
                            -> forall (t : API.type) (rc : bool) (e : API.expr t),
                              valid_expr_bool_step (@valid_expr_bool) t rc e = true -> valid_expr rc e
                          := _ in
                      let valid_expr_bool_step_correct := _ in*)
                      let valid_expr_bool_correct := _ in
                      existT
                        _ (@valid_expr_bool_step)
                        (existT
                           _ (@valid_expr_bool)
                           ((fun t rc e
                             => (*iff_reflect
                                  _ _
                                  (conj*) (valid_expr_bool_correct t rc e)
                                        (*((fix valid_expr_bool_correct' {t} (rc : bool) (e : API.expr t) {struct e} := valid_expr_bool_step_correct (@valid_expr_bool_correct') t rc e) t rc e))*)),
                            valid_expr_bool_eta)));
       [ revert valid_expr_bool t rc e
       | clear -p; intros ? ? e; destruct e; cbn [valid_expr_bool]; reflexivity
       (*| clearbody valid_expr_bool_eta
       | clearbody valid_expr_bool_eta valid_expr_bool_step_correct';
         let H := fresh in
         intro H; specialize (valid_expr_bool_step_correct' H);
         intros t rc e;
         pose e as e';
         destruct e;
         let e' := (eval cbv delta [e'] in e') in
         refine (valid_expr_bool_step_correct' _ rc e')*)
       | (*clear valid_expr_bool_step_correct' valid_expr_bool_step_correct;*)
         clearbody valid_expr_bool_eta;
         intros t rc e H;
         induction H;
         rewrite valid_expr_bool_eta; clear valid_expr_bool_eta;
         clearbody valid_expr_bool;
         cbv [valid_expr_bool_step];
         clear valid_expr_bool_step;
         split_lists;
         lazymatch goal with
         | [ |- ?ev ?veb ?t ?rc ?e = true ]
           => let subcall := fresh "subcall" in
              let ty := type of ev in
              let H := fresh in
              let rcv := lazymatch rc with
                         | true => constr:(Some true)
                         | false => constr:(Some false)
                         | _ => constr:(@None bool)
                         end in
              simple refine (let subcall : ty := _ in
                             let H : subcall veb t rc e = true := _ in
                             _);
              [ clear -p;
                let t := fresh "t" in
                let rc := fresh "rc" in
                let e := fresh "e" in
                intros valid_expr_bool t rc e;
                lazymatch rcv with
                | Some true => refine (andb rc _)
                | Some false => refine (andb (negb rc) _)
                | None => idtac
                end;
                revert e; shelve
              | subst subcall; cbv beta;
                lazymatch goal with
                | [ |- andb _ _ = true ] => apply andb_true_intro; split; [ reflexivity | ]
                | [ |- _ = true ] => idtac
                end;
                fill_valid_expr_bool_after_split_lists
              | let T := type of subcall in
                let subcall' := fresh "subcall'" in
                simple refine (let subcall' : T := _ in
                               _);
                [ clear -subcall;
                  let subcall_body := (eval cbv beta iota delta [subcall] in subcall) in
                  clear subcall;
                  transparent_abstract (exact subcall_body)
                | let subcallv := (eval cbv delta [subcall'] in subcall') in
                  instantiate (1:=subcallv);
                  replace subcallv with subcall by reflexivity;
                  refine H ] ]
         end ]).
    intros; exact nil.
  Defined.

  Definition valid_expr_bool_step
    : forall (valid_expr_bool : forall {t} (rc : bool) (e : API.expr t), bool)
             {t} (rc : bool) (e : API.expr t), bool
    := Eval cbv [projT1 valid_expr_bool_package] in projT1 valid_expr_bool_package.

  Fixpoint valid_expr_bool {t} (rc : bool) (e : API.expr t) {struct e} : bool
    := @valid_expr_bool_step (@valid_expr_bool) t rc e.

  Lemma valid_expr_bool_eta {t} (rc : bool) (e : API.expr t)
    : valid_expr_bool rc e = @valid_expr_bool_step (@valid_expr_bool) t rc e.
  Proof using Type. now destruct e. Qed.

  Lemma valid_expr_bool_impl2
    : forall {t} (rc : bool) (e : API.expr t),
      valid_expr rc e -> valid_expr_bool rc e = true.
  Proof using Type. exact (fst (projT2 (projT2 valid_expr_bool_package))). Qed.

  Definition valid_expr_bool_impl1_step
             (valid_expr_bool_correct
              : forall {t} (rc : bool) (e : API.expr t),
                 valid_expr_bool rc e = true -> valid_expr rc e)
             {t} (rc : bool) (e : API.expr t)
    : valid_expr_bool rc e = true -> valid_expr rc e.
  Proof using Type.
    clear p_ok.
    rewrite valid_expr_bool_eta.
    cbv [valid_expr_bool_step].
    lazymatch goal with
    | [ |- fold_left orb ?ls ?b = true -> _ ]
      => induction_fold_left_orb_true ls b
    end.
    all: lazymatch goal with
         | [ |- false = true -> _ ]
           => let H := fresh in
              intro H; exfalso; clear -H; discriminate
         | [ |- ?lhs = true -> valid_expr _ _ ]
           => let h := head lhs in
              cbv [h]
         end.
    Time
      all: intro;
  repeat match goal with
         | [ H : andb _ _ = true |- _ ] => apply andb_prop in H; destruct H
    end.
    Time all: let valid_expr_bool_correct := get_valid_expr_bool_correct (@valid_expr_bool) in
              repeat (let H := match goal with
                               | [ H : ?lhs = true |- _ ]
                                 => let __ := match lhs with context[valid_expr_bool] => idtac end in
                                    H
                               end in
                      let H' := fresh in
                      eassert (H' : _);
                     [ instantiate (1:=ltac:(clear H));
                     repeat match goal with
                            | [ H' : _ |- _ ] => tryif first [ constr_eq H H' | constr_eq H' valid_expr_bool_correct ] then fail else clear H'
                            end;
                     repeat match type of H with
                            | context[match ?e with _ => _ end]
                              => is_var e;
                     instantiate (1:=ltac:(destruct e)); destruct e
                     | false = true => refine (_ : False); clear -H; discriminate
                       end;
                     lazymatch type of H with
                     | @valid_expr_bool _ _ _ = true
                       => refine (valid_expr_bool_correct _ _ _ H)
                     | ?T => fail 1 "Leftover:" T
                     end
                     | clear H ]).
    all: clear valid_expr_bool_correct.
    Time all:
      time
        abstract (
          time repeat early_safe_step;
        time repeat first [ early_safe_step
                          | progress subst
                          | match goal with
                            | [ H : negb ?x = ?y |- _ ]
                              => let H' := fresh in
                                 assert (H' : x = negb y) by (clear -H; now destruct x, y);
                          cbn [negb] in H'; clear H
                            end
                          | expr.invert_match_step
                          | match goal with
                            | [ H : context[match ?x with _ => _ end ] |- _ ]
                              => is_var x;
                          lazymatch type of x with
                          | ?F ?t
                            => lazymatch type of t with
                               | API.type
                                 => type.invert_one x; subst; inversion_type
                            end
                            end
                            end
                          | match goal with
                            | [ H : ?x = ?x |- _ ] => clear H
                            | [ H : ?x = ?v |- _ ]
                              => let b := lazymatch v with true => x | false => constr:(negb x) end in
                                 lazymatch constr:(@id (reflect _ b) _) with
                                 | @id (reflect (?x = ?x) _) _
                                   => clear H
                                 | @id (reflect ?P _) ?lem
                                   => unique assert P;
                          [ let H' := fresh in
                            pose proof lem as H'; rewrite H in H'; cbn [negb] in H';
                          inversion H'; assumption
                          | ]
                            end
                            end ];
    (* Tactic call ran for 2.641 secs (2.628u,0.011s) (success)
Tactic call ran for 23.769 secs (23.632u,0.135s) (success)
Tactic call ran for 1.041 secs (1.029u,0.012s) (success)
Tactic call ran for 1.06 secs (1.048u,0.011s) (success)
Tactic call ran for 1.602 secs (1.598u,0.003s) (success)
Tactic call ran for 0.002 secs (0.002u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 8.624 secs (8.58u,0.043s) (success)
Tactic call ran for 5.875 secs (5.843u,0.031s) (success)
Tactic call ran for 5.916 secs (5.916u,0.s) (success)
Tactic call ran for 18.244 secs (18.244u,0.s) (success)
Tactic call ran for 17.057 secs (17.057u,0.s) (success)
Tactic call ran for 6.049 secs (6.049u,0.s) (success)
Tactic call ran for 12.284 secs (12.284u,0.s) (success)
Tactic call ran for 0.887 secs (0.887u,0.s) (success)
Tactic call ran for 0.649 secs (0.649u,0.s) (success)

Finished transaction in 105.706 secs (105.453u,0.252s) (successful)
     *)
        constructor; solve [ eauto ]
        ).
    (* Tactic call ran for 282.124 secs (281.901u,0.224s) (success) *)
    Time Defined.
  (*Finished transaction in 76.9 secs (76.9u,0.s) (successful)*)

  Time Fixpoint valid_expr_bool_impl1 {t} (rc : bool) (e : API.expr t) {struct e}
    : valid_expr_bool rc e = true -> valid_expr rc e
    := @valid_expr_bool_impl1_step (@valid_expr_bool_impl1) t rc e.
  (* Finished transaction in 0.387 secs (0.387u,0.s) (successful) *)

  Lemma valid_expr_bool_iff {t} (e : API.expr (type.base t)) :
    forall rc,
      valid_expr_bool rc e = true <-> valid_expr rc e.
  Proof.
    split; eauto using valid_expr_bool_impl1, valid_expr_bool_impl2.
  Qed.
End Expr.
