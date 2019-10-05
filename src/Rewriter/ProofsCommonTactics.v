Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.UnderLetsProofs.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Language.IdentifiersLibraryProofs.
Require Import Crypto.Rewriter.Rewriter.
Require Import Crypto.Rewriter.ProofsCommon.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.CPSId.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.FMapPositive.Equality.
Require Import Crypto.Util.MSetPositive.Equality.
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Sigma.Related.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Logic.ExistsEqAnd.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.NatUtil.
Require Crypto.Util.PrimitiveHList.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.
  Import expr.Notations.
  Export Rewriter.ProofsCommon.Compilers.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.
    Export Rewriter.ProofsCommon.Compilers.RewriteRules.

    Ltac warn_if_goals_remain _ :=
      [ > idtac "WARNING: Remaining goal:"; print_context_and_goal () .. ].

    Module Import WfTactics.
      Export Rewriter.ProofsCommon.Compilers.RewriteRules.WfTactics.
      Module Export Settings.
        Global Strategy -100 [rewrite_rules Compile.rewrite_rules_goodT_curried_cps].
      End Settings.

      Ltac start_good _ :=
        lazymatch goal with
        | [ |- context[@Wf_GoalT ?exprInfo ?exprExtraInfo ?pkg] ]
          => let pkg' := (eval hnf in pkg) in
             change pkg with pkg';
             let exprInfo' := (eval hnf in exprInfo) in
             change exprInfo with exprInfo'
        end;
        let exprInfo := lazymatch goal with |- context[@Wf_GoalT ?exprInfo ?exprExtraInfo ?pkg] => (eval hnf in exprInfo) end in
        let exprExtraInfo := lazymatch goal with |- context[@Wf_GoalT ?exprInfo ?exprExtraInfo ?pkg] => (eval hnf in exprExtraInfo) end in
        cbv [Wf_GoalT]; Compilers.pattern.ident.GoalType.red_proj; intros;
        lazymatch constr:((exprInfo, exprExtraInfo)) with
        | ({| Classes.base_interp := ?base_interp
           |}
           , {| Classes.base_beq := ?base_beq
                ; Classes.reflect_base_beq := ?reflect_base_beq
                ; Classes.try_make_transport_base_cps_correct := ?try_make_transport_base_cps_correct
             |})
          => let base_interp_head := head base_interp in
             match goal with
             | [ |- @Compile.rewrite_rules_goodT ?base ?try_make_transport_base_cps ?ident ?pident ?pident_arg_types ?var1 ?var2 ?rew1 ?rew2 ]
               => let H := fresh in
                  pose proof (@Compile.rewrite_rules_goodT_by_curried base base_beq reflect_base_beq try_make_transport_base_cps try_make_transport_base_cps_correct ident pident pident_arg_types var1 var2 rew1 rew2 eq_refl) as H;
                  let data := lazymatch rew1 with Make.GoalType.rewrite_rules ?data _ => data end in
                  let data' := (eval hnf in data) in
                  change data with data' in H;
                  cbv [Make.GoalType.rewrite_rules] in H;
                  let h' := lazymatch type of H with
                            | context[Compile.rewrite_rules_goodT_curried_cps ?pident_arg_types ?rew1] => head rew1
                            end in
                  let pident_arg_types' := (eval cbv -[base.interp base_interp_head] in pident_arg_types) in
                  change pident_arg_types with pident_arg_types' in H;
                  cbv [h' Compile.rewrite_rules_goodT_curried_cps] in H;
                  (* make [Qed] not take forever by explicitly recording a cast node *)
                  let H' := fresh in
                  pose proof H as H'; clear H;
                  apply H'; clear H'; intros
             end
        end.

      Ltac fin_wf :=
        repeat first [ progress intros
                     | match goal with
                       | [ |- expr.wf _ (_ @ _) (_ @ _) ] => constructor
                       | [ |- expr.wf _ (#_) (#_) ] => constructor
                       | [ |- expr.wf _ ($_) ($_) ] => constructor
                       | [ |- expr.wf _ (expr.Abs _) (expr.Abs _) ] => constructor; intros
                       | [ H : @List.In ?T _ ?ls |- _ ] => is_evar ls; unify ls (@nil T); cbn [List.In] in H
                       | [ |- List.In ?v ?ls ] => is_evar ls; instantiate (1:=cons v _)
                       end
                     | progress subst
                     | progress destruct_head'_or
                     | progress destruct_head'_False
                     | progress inversion_sigma
                     | progress inversion_prod
                     | assumption
                     | esplit; revgoals; solve [ fin_wf ]
                     | econstructor; solve [ fin_wf ]
                     | progress cbn [List.In fst snd eq_rect] in * ].

      Ltac handle_reified_rewrite_rules exprExtraInfo :=
        repeat
          first [ match goal with
                  | [ |- option_eq _ ?x ?y ]
                    => lazymatch x with Some _ => idtac | None => idtac end;
                       lazymatch y with Some _ => idtac | None => idtac end;
                       progress cbn [option_eq]
                  | [ |- UnderLets.wf _ _ (Reify.expr_value_to_rewrite_rule_replacement ?rii1 ?sda _) (Reify.expr_value_to_rewrite_rule_replacement ?rii2 ?sda _) ]
                    => apply (@Reify.wf_expr_value_to_rewrite_rule_replacement _ exprExtraInfo _ _ sda); intros
                  | [ |- ?x = ?x ] => reflexivity
                  end
                | break_innermost_match_step
                | progress cbv [Compile.wf_maybe_do_again_expr] in *
                | progress fin_wf ].

      Ltac handle_extra_nbe exprExtraInfo :=
        repeat first [ match goal with
                       | [ |- expr.wf ?G (reify_list ?e1) (reify_list ?e2) ]
                         => refine (proj2 (expr.wf_reify_list (buildIdent := @Classes.buildIdent _ exprExtraInfo) (reflect_base_beq := @Classes.reflect_base_beq _ exprExtraInfo) G e1 e2) _)
                       | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
                       | [ |- List.Forall2 _ (List.map _ _) (List.map _ _) ] => rewrite Forall2_map_map_iff
                       | [ |- List.Forall _ (seq _ _) ] => rewrite Forall_seq
                       end
                     | progress intros
                     | progress fin_wf ].

      Ltac handle_extra_arith_rules :=
        repeat first [ progress cbv [option_eq] in *
                     | break_innermost_match_step
                     | match goal with
                       | [ Hwf : Compile.wf_value _ ?x _, H : context[SubstVarLike.is_recursively_var_or_ident _ ?x] |- _ ] => erewrite SubstVarLike.wfT_is_recursively_var_or_ident in H by exact Hwf
                       end
                     | congruence
                     | progress fin_wf ].


      Module Export Tactic.
        Export Settings.

        Ltac prove_good _ :=
          let do_time := Make.time_if_debug1 in (* eval the level early *)
          let exprExtraInfo := lazymatch goal with |- context[@Wf_GoalT ?exprInfo ?exprExtraInfo ?pkg] => exprExtraInfo end in
          do_time start_good;
          do_time ltac:(fun _ => handle_reified_rewrite_rules exprExtraInfo; handle_extra_nbe exprExtraInfo; handle_extra_arith_rules);
          warn_if_goals_remain ().
      End Tactic.
    End WfTactics.

    Module InterpTactics.
      Import Crypto.Util.ZRange.
      Export Rewriter.ProofsCommon.Compilers.RewriteRules.InterpTactics.

      (** Coq >= 8.9 is much better at [eapply] than Coq <= Coq 8.8 *)
      Ltac cbv_type_for_Coq88 T :=
        lazymatch eval hnf in T with
        | @eq ?T ?A ?B => let A' := (eval cbv [ident.Thunked.bool_rect ident.Thunked.list_case ident.Thunked.list_rect ident.Thunked.nat_rect ident.Thunked.option_rect] in A) in
                          constr:(@eq T A' B)
        | forall x : ?A, ?P
          => let P' := fresh in
             constr:(forall x : A,
                        match P return Prop with
                        | P'
                          => ltac:(let v := cbv_type_for_Coq88 P' in
                                   exact v)
                        end)
        end.
      Ltac cbv_for_Coq88_in H :=
        cbv [ident.Thunked.bool_rect ident.Thunked.list_case ident.Thunked.list_rect ident.Thunked.nat_rect ident.Thunked.option_rect];
        let T := type of H in
        let T := cbv_type_for_Coq88 T in
        change T in H.

      Ltac start_interp_good _ :=
        lazymatch goal with
        | [ |- context[@Interp_GoalT ?exprInfo ?exprExtraInfo ?pkg] ]
          => let pkg' := (eval hnf in pkg) in
             change pkg with pkg';
             let exprInfo' := (eval hnf in exprInfo) in
             change exprInfo with exprInfo'
        end;
        let exprInfo := lazymatch goal with |- context[@Interp_GoalT ?exprInfo ?exprExtraInfo ?pkg] => (eval hnf in exprInfo) end in
        let exprExtraInfo := lazymatch goal with |- context[@Interp_GoalT ?exprInfo ?exprExtraInfo ?pkg] => (eval hnf in exprExtraInfo) end in
        cbv [List.skipn Interp_GoalT] in *; Compilers.pattern.ident.GoalType.red_proj; intros;
        lazymatch constr:((exprInfo, exprExtraInfo)) with
        | ({| Classes.ident_interp := ?ident_interp
           |}
           , {| Classes.base_beq := ?base_beq
                ; Classes.reflect_base_beq := ?reflect_base_beq
                ; Classes.try_make_transport_base_cps_correct := ?try_make_transport_base_cps_correct
             |})
          => let ident_interp_head := head ident_interp in
             lazymatch goal with
             | [ |- @Compile.rewrite_rules_interp_goodT ?base ?try_make_transport_base_cps ?ident ?pident ?pident_arg_types ?pident_to_typed ?base_interp ?ident_interp (Make.GoalType.rewrite_rules ?data ?var) ]
               => let base_interp_head := head base_interp in
                  let H := fresh in
                  pose proof (@Compile.rewrite_rules_interp_goodT_by_curried
                                base base_beq reflect_base_beq try_make_transport_base_cps try_make_transport_base_cps_correct ident pident pident_arg_types pident_to_typed base_interp ident_interp (Make.GoalType.rewrite_rules data var) (rewrite_rules_specs data)) as H;
                  let data' := (eval hnf in data) in
                  change data with data' in * |- ;
                  cbv [Make.GoalType.rewrite_rules dummy_count rewrite_rules_specs] in * |- ;
                  let h' := lazymatch type of H with context[Compile.rewrite_rules_interp_goodT_curried_cps _ _ _ ?v] => head v end in
                  unfold h' in H at 1;
                  let pident_arg_types' := (eval cbv -[base.interp base_interp_head] in pident_arg_types) in
                  change pident_arg_types with pident_arg_types' in H;
                  let pident_to_typed' := (eval cbv -[pattern.type.subst_default pattern.base.subst_default List.fold_right base.interp base_interp_head Datatypes.fst Datatypes.snd] in pident_to_typed) in
                  let pident_to_typed' := (eval cbn [Datatypes.fst Datatypes.snd List.fold_right] in pident_to_typed') in
                  change pident_to_typed with pident_to_typed' in H;
                  cbv [Compile.rewrite_rules_interp_goodT_curried_cps
                         Classes.base Classes.ident Classes.ident_interp Classes.base_interp Classes.ident_interp
                         ident.literal ident.eagerly] in H;
                  cbn [fst snd hd tl projT1 projT2] in H;
                  (* make [Qed] not take forever by explicitly recording a cast node *)
                  let H' := fresh in
                  pose proof H as H'; clear H;
                  apply H'; clear H'
             end;
             [ try assumption;
               cbn [PrimitiveHList.hlist snd];
               repeat lazymatch goal with
                      | [ |- PrimitiveProd.Primitive.prod _ _ ] => constructor
                      | [ |- forall A x, x = x ] => reflexivity
                      end;
               try assumption
             | try match goal with
                   | [ H : PrimitiveHList.hlist _ _ |- _ ] => clear H
                   end;
               let H := fresh in
               intro H; hnf in H;
               repeat first [ progress intros
                            | match goal with
                              | [ |- { pf : ?x = ?x | _ } ] => (exists eq_refl)
                              | [ |- True /\ _ ] => split; [ exact I | ]
                              | [ |- _ /\ _ ] => split; [ intros; exact I | ]
                              | [ |- match (if ?b then _ else _) with Some _ => _ | None => _ end ]
                                => destruct b eqn:?
                              | [ |- True ] => exact I
                              end
                            | progress eta_expand
                            | progress cbn [eq_rect] in * ];
               cbn [fst snd base.interp type.interp projT1 projT2 UnderLets.interp expr.interp type.related ident_interp_head] in *;
               cbn [fst snd] in *;
               eta_expand;
               split_andb;
               repeat match goal with
                      | [ H : ?b = true |- _ ] => unique pose proof (@Reflect.reflect_bool _ b _ H)
                      | [ H : negb _ = false |- _ ] => rewrite Bool.negb_false_iff in H
                      | [ H : _ = false |- _ ] => rewrite <- Bool.negb_true_iff in H
                      end;
               subst; cbv [ident.gets_inlined ident.literal] in *;
               lazymatch goal with
               | [ |- ?R ?v ]
                 => let v' := open_constr:(_) in
                    replace v with v';
                    [ | symmetry;
                        cbv_for_Coq88_in H;
                        unshelve eapply H; shelve_unifiable;
                        try eassumption;
                        try (repeat apply conj; assumption);
                        try match goal with
                            | [ |- ?A = ?B ] => first [ is_evar A | is_evar B ]; reflexivity
                            | [ |- ?T ] => is_evar T; exact I
                            | [ |- ?P ] (* TODO: Maybe we shouldn't simplify boolean expressions in rewriter reification, since we end up just having to undo it here in a kludgy way....... *)
                              => apply (proj2 (@Bool.reflect_iff P _ _));
                                 progress rewrite ?Bool.eqb_true_l, ?Bool.eqb_true_r, ?Bool.eqb_false_l, ?Bool.eqb_false_r;
                                 let b := lazymatch goal with |- ?b = true => b end in
                                 apply (proj1 (@Bool.reflect_iff _ b _));
                                 tauto
                            end ];
                    clear H
               end;
               fold (@base.interp) in *
                                      .. ]
        end.

      Ltac recurse_interp_related_step ident_interp_head ident_interp_Proper :=
        let do_replace v :=
            ((tryif is_evar v then fail else idtac);
             let v' := open_constr:(_) in
             let v'' := fresh in
             cut (v = v'); [ generalize v; intros v'' ?; subst v'' | symmetry ]) in
        match goal with
        | _ => progress cbv [expr.interp_related] in *
        | _ => progress cbn [Compile.reify_expr]
        | [ |- context[(fst ?x, snd ?x)] ] => progress eta_expand
        | [ |- context[match ?x with pair a b => _ end] ] => progress eta_expand
        | [ |- expr.interp_related_gen ?ident_interp ?R ?f ?v ]
          => do_replace v
        | [ |- exists (fv : ?T1 -> ?T2) (ev : ?T1),
              _ /\ _ /\ fv ev = ?x ]
          => lazymatch T1 with Z => idtac | (Z * Z)%type => idtac end;
             lazymatch T2 with Z => idtac | (Z * Z)%type => idtac end;
             first [ do_replace x
                   | is_evar x; do 2 eexists; repeat apply conj; [ | | reflexivity ] ]
        | _ => progress intros
        | [ |- expr.interp_related_gen _ _ _ ?ev ] => is_evar ev; eassumption
        | [ |- expr.interp_related_gen _ _ (?f @ ?x) ?ev ]
          => is_evar ev;
             let fh := fresh in
             let xh := fresh in
             set (fh := f); set (xh := x); cbn [expr.interp_related_gen]; subst fh xh;
             do 2 eexists; repeat apply conj; [ | | reflexivity ]
        | [ |- expr.interp_related_gen _ _ (expr.Abs ?f) _ ]
          => let fh := fresh in set (fh := f); cbn [expr.interp_related_gen]; subst fh
        | [ |- expr.interp_related_gen _ _ (expr.Ident ?idc) ?ev ]
          => is_evar ev;
             cbn [expr.interp_related_gen]; apply ident_interp_Proper; reflexivity
        | [ |- _ = _ :> ?T ]
          => lazymatch T with
             | BinInt.Z => idtac
             | (BinInt.Z * BinInt.Z)%type => idtac
             end;
             progress cbn [ident_interp_head fst snd]
        | [ |- ?x = ?y ] => tryif first [ has_evar x | has_evar y ] then fail else (progress subst)
        | [ |- ?x = ?y ] => tryif first [ has_evar x | has_evar y ] then fail else reflexivity
        | [ |- ?x = ?x ] => tryif has_evar x then fail else reflexivity
        | [ |- ?ev = _ ] => is_evar ev; reflexivity
        | [ |- _ = ?ev ] => is_evar ev; reflexivity
        end.

      (* TODO: MOVE ME? *)
      Ltac recursive_match_to_case term :=
        let contains_match x
            := lazymatch x with
               | context[match _ with nil => _ | _ => _ end] => true
               | context[match _ with pair a b => _ end] => true
               | context[match _ with true => _ | false => _ end] => true
               | _ => false
               end in
        lazymatch term with
        | context G[match ?ls with nil => ?N | cons x xs => @?C x xs end]
          => let T := type of N in
             let term := context G[list_case (fun _ => T) N C ls] in
             recursive_match_to_case term
        | context G[match ?v with pair a b => @?P a b end]
          => let T := lazymatch type of P with forall a b, @?T a b => T end in
             let term := context G[prod_rect (fun ab => T (fst ab) (snd ab)) P v] in
             recursive_match_to_case term
        | context G[match ?b with true => ?t | false => ?f end]
          => let T := type of t in
             let term := context G[bool_rect (fun _ => T) t f b] in
             recursive_match_to_case term
        | _ => let has_match := contains_match term in
               match has_match with
               | true
                 => let G_f
                        := match term with
                           | context G[fun x : ?T => @?f x]
                             => let has_match := contains_match f in
                                lazymatch has_match with
                                | true
                                  => let f' := fresh in
                                     let T' := type of f in
                                     constr:(((fun f' : T' => ltac:(let G' := context G[f'] in exact G')),
                                              f))
                                end
                           end in
                    lazymatch G_f with
                    | ((fun f' => ?G), (fun x : ?T => ?f))
                      => let x' := fresh in
                         let rep := constr:(fun x' : T
                                            => ltac:(let f := constr:(match x' with x => f end) in
                                                     let f := recursive_match_to_case f in
                                                     exact f)) in
                         let term := constr:(match rep with f' => G end) in
                         recursive_match_to_case term
                    end
               | false
                 => term
               end
        end.
      Ltac recursive_match_to_case_in_goal :=
        let G := match goal with |- ?G => G end in
        let G := recursive_match_to_case G in
        change G.

      Ltac preprocess_step base_interp_head :=
        first [ progress cbv [expr.interp_related respectful ident.literal ident.eagerly] in *
              | progress cbn [fst snd base.interp base_interp_head Compile.value'] in *
              | progress intros
              | progress subst
              | match goal with
                | [ |- context[match _ with nil => _ | _ => _ end] ] => progress recursive_match_to_case_in_goal
                | [ |- context[match _ with pair a b => _ end] ] => progress recursive_match_to_case_in_goal
                | [ |- context[match _ with true => _ | false => _ end] ] => progress recursive_match_to_case_in_goal
                | [ |- context[match invert_expr.reflect_list ?ls with _ => _ end] ]
                  => destruct (invert_expr.reflect_list ls) eqn:?
                | [ |- context G[expr.interp_related_gen ?ident_interp (fun t : ?T => ?vii t ?b)] ]
                  => progress change (fun t : T => vii t b) with (fun t : T => @Compile.value_interp_related _ _ _ ident_interp t b)
                end ].
      Ltac preprocess base_interp_head := repeat preprocess_step base_interp_head.

      Ltac handle_extra_nbe exprExtraInfo ident_interp_head ident_interp_Proper :=
        repeat match goal with
               | [ |- UnderLets.interp_related _ _ (UnderLets.Base (expr.Ident _)) _ ]
                 => cbn [UnderLets.interp_related UnderLets.interp_related_gen expr.interp_related_gen ident_interp_head type.related]; reflexivity
               | [ |- UnderLets.interp_related _ _ (UnderLets.Base (reify_list ?LS)) ?V ]
                 => cbn [UnderLets.interp_related UnderLets.interp_related_gen];
                    refine (proj2 (expr.reify_list_interp_related_gen_iff (buildInterpIdentCorrect:=@Classes.buildInterpIdentCorrect _ exprExtraInfo) (ls:=LS) (v:=V)) _)
               | [ |- UnderLets.interp_related ?ident_interp _ (UnderLets.Base ?e) ?x ]
                 => lazymatch (eval cbn [expr.interp ident_interp_head] in (expr.interp ident_interp e)) with
                    | (_, _) =>
                      cbn [UnderLets.interp_related UnderLets.interp_related_gen];
                      recurse_interp_related_step ident_interp_head ident_interp_Proper;
                      [ recurse_interp_related_step ident_interp_head ident_interp_Proper
                      | lazymatch x with
                        | (_, _) => reflexivity
                        | _ => etransitivity; [ | symmetry; apply surjective_pairing ]; reflexivity
                        end ];
                      [ | reflexivity ]; cbn [fst snd];
                      recurse_interp_related_step ident_interp_head ident_interp_Proper; [ recurse_interp_related_step ident_interp_head ident_interp_Proper | reflexivity ]
                    end
               | [ |- List.Forall2 _ (List.map _ _) _ ]
                 => rewrite Forall2_map_l_iff
               | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
               | [ |- List.Forall _ _ ] => rewrite Forall_forall; intros
               | [ |- expr.interp_related_gen _ _ (expr.Ident _) _ ]
                 => cbn [expr.interp_related_gen ident_interp_head type.related]; reflexivity
               end.

      Ltac fin_tac :=
        repeat first [ assumption
                     | progress change S with Nat.succ
                     | progress cbv [ident.literal ident.eagerly ident.cast2] in *
                     | progress cbn [fst snd] in *
                     | match goal with
                       | [ |- ?x = ?x ] => reflexivity
                       | [ |- _ = _ ] => reflexivity
                       end ].

      Ltac handle_reified_rewrite_rules_interp exprInfo exprExtraInfo base_interp_head ident_interp_head ident_interp_Proper :=
        let not_arrow t := lazymatch t with _ -> _ => fail | _ => idtac end in
        repeat first [ assumption
                     | match goal with
                       | [ |- UnderLets.interp_related _ _ (Reify.expr_value_to_rewrite_rule_replacement _ ?sda _) _ ]
                         => refine (@Reify.expr_value_to_rewrite_rule_replacement_interp_related exprInfo exprExtraInfo sda _ _ _ _);
                            cbv [Classes.base Classes.ident Classes.ident_interp Classes.base_interp Classes.ident_interp]

                       | [ |- UnderLets.interp_related_gen ?ii ?R (UnderLets.Base (#_(*ident.ident_list_rect*) @ _ @ _ @ _)%expr) (@list_rect ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => not_arrow P; progress change (@list_rect A (fun _ => P) N C ls) with (@ident.Thunked.list_rect A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_list_rect*) @ _ @ _ @ _)%expr (@list_rect ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => not_arrow P; progress change (@list_rect A (fun _ => P) N C ls) with (@ident.Thunked.list_rect A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_eager_list_rect*) @ _ @ _ @ _)%expr (@list_rect ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => not_arrow P; progress change (@list_rect A (fun _ => P) N C ls) with (@ident.Thunked.list_rect A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_list_case*) @ _ @ _ @ _)%expr (@list_case ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => not_arrow P; progress change (@list_case A (fun _ => P) N C ls) with (@ident.Thunked.list_case A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_nat_rect*) @ _ @ _ @ _)%expr (@nat_rect (fun _ => ?P) ?N ?C ?ls) ]
                         => not_arrow P; progress change (@nat_rect (fun _ => P) N C ls) with (@ident.Thunked.nat_rect P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_eager_nat_rect*) @ _ @ _ @ _)%expr (@nat_rect (fun _ => ?P) ?N ?C ?ls) ]
                         => not_arrow P; progress change (@nat_rect (fun _ => P) N C ls) with (@ident.Thunked.nat_rect P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_bool_rect*) @ _ @ _ @ _)%expr (@bool_rect (fun _ => ?P) ?T ?F ?b) ]
                         => not_arrow P; progress change (@bool_rect (fun _ => P) T F b) with (@ident.Thunked.bool_rect P (fun _ => T) (fun _ => F) b)
                       | [ |- expr.interp_related_gen ?ii ?R (#_(*ident.ident_option_rect*) @ _ @ _ @ _)%expr (@option_rect ?A (fun _ => ?P) ?S ?N ?o) ]
                         => not_arrow P; progress change (@option_rect A (fun _ => P) S N o) with (@ident.Thunked.option_rect A P S (fun _ => N) o)

                       | [ |- match ?x with pair _ _ => _ end = prod_rect _ _ _ ]
                         => cbv [prod_rect]; eta_expand

                       | [ |- expr.interp_related_gen _ _ (expr.Var _) _ ]
                         => cbn [expr.interp_related_gen]
                       | [ |- expr.interp_related_gen _ _ (expr.Ident ?idc) ?rhs ]
                         => let rhs' := open_constr:(_) in
                            replace rhs with rhs';
                            [ cbn [expr.interp_related_gen]; now refine (ident_interp_Proper _ idc idc eq_refl)
                            | try reflexivity ]
                       | [ |- expr.interp_related_gen _ _ (expr.Abs ?f) _ ]
                         => let fh := fresh in set (fh := f); cbn [expr.interp_related_gen]; subst fh; cbv beta; intros
                       | [ |- expr.interp_related_gen _ _ (expr.LetIn ?v ?f) (LetIn.Let_In ?V ?F) ]
                         => let vh := fresh in
                            set (vh := v);
                            let fh := fresh in
                            set (fh := f);
                            cbn [expr.interp_related_gen]; subst fh vh; cbv beta;
                            exists F, V; repeat apply conj; intros
                       | [ |- expr.interp_related_gen _ _ (?f @ ?x)%expr (?F ?X) ]
                         => let fh := fresh in
                            set (fh := f);
                            let xh := fresh in
                            set (xh := x);
                            cbn [expr.interp_related_gen]; subst fh xh;
                            exists F, X; repeat apply conj; [ | | reflexivity ]

                       | [ |- _ = _ ] => solve [ fin_tac ]
                       | [ |- type.eqv _ _ ] => cbn [ident_interp_head type.related]; cbv [respectful]; intros; subst
                       end
                     | progress repeat (do 2 eexists; repeat apply conj; [ | | reflexivity ]) ].

      Module Export Tactic.
        Ltac prove_interp_good _ :=
          let do_time := Make.time_if_debug1 in (* eval the level early *)
          let exprInfo := lazymatch goal with |- context[@Interp_GoalT ?exprInfo ?exprExtraInfo ?pkg] => (eval hnf in exprInfo) end in
          let exprExtraInfo := lazymatch goal with |- context[@Interp_GoalT ?exprInfo ?exprExtraInfo ?pkg] => (eval hnf in exprExtraInfo) end in
          lazymatch constr:((exprInfo, exprExtraInfo)) with
          | ({| Classes.base_interp := ?base_interp
                ; Classes.ident_interp := ?ident_interp
             |}
             , {| Classes.ident_interp_Proper := ?ident_interp_Proper
               |})
            => let base_interp_head := head base_interp in
               let ident_interp_head := head ident_interp in
               do_time start_interp_good;
               do_time
                 ltac:(
                 fun _
                 => preprocess base_interp_head;
                    handle_extra_nbe exprExtraInfo ident_interp_head ident_interp_Proper;
                    handle_reified_rewrite_rules_interp exprInfo exprExtraInfo base_interp_head ident_interp_head ident_interp_Proper)
          end;
          warn_if_goals_remain ().
      End Tactic.
    End InterpTactics.
  End RewriteRules.
End Compilers.
