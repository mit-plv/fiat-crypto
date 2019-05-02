Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.LanguageWf.
Require Import Crypto.UnderLetsProofs.
Require Import Crypto.IdentifiersLibrary.
Require Import Crypto.IdentifiersLibraryProofs.
Require Import Crypto.Rewriter.
Require Import Crypto.RewriterWf1.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.CPSId.
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
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.
  Import expr.Notations.
  Import defaults.
  Export RewriterWf1.Compilers.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.
    Export RewriterWf1.Compilers.RewriteRules.

    Module Import WfTactics.
      Export RewriterWf1.Compilers.RewriteRules.WfTactics.
      Module Export Settings.
        Global Strategy -100 [rewrite_rules Compile.rewrite_rules_goodT_curried_cps].
      End Settings.

      Ltac start_good _ :=
        lazymatch goal with
        | [ |- context[@Wf_GoalT ?pkg] ]
          => let pkg' := (eval hnf in pkg) in
             replace pkg with pkg' by reflexivity
        end;
        cbv [Wf_GoalT]; Compilers.pattern.ident.GoalType.red_proj; intros;
        match goal with
        | [ |- @Compile.rewrite_rules_goodT ?ident ?pident ?pident_arg_types ?var1 ?var2 ?rew1 ?rew2 ]
          => let H := fresh in
             pose proof (@Compile.rewrite_rules_goodT_by_curried ident pident pident_arg_types var1 var2 rew1 rew2 eq_refl) as H;
             let data := lazymatch rew1 with Make.GoalType.rewrite_rules ?data _ => data end in
             let data' := (eval hnf in data) in
             change data with data' in H;
             cbv [Make.GoalType.rewrite_rules] in H;
             let h' := lazymatch type of H with
                       | context[Compile.rewrite_rules_goodT_curried_cps ?pident_arg_types ?rew1] => head rew1
                       end in
             let pident_arg_types' := (eval cbv -[base.interp] in pident_arg_types) in
             change pident_arg_types with pident_arg_types' in H;
             cbv [h' Compile.rewrite_rules_goodT_curried_cps] in H;
             (* make [Qed] not take forever by explicitly recording a cast node *)
             let H' := fresh in
             pose proof H as H'; clear H;
             apply H'; clear H'; intros
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

      Ltac handle_reified_rewrite_rules :=
        repeat
          first [ match goal with
                  | [ |- option_eq _ ?x ?y ]
                    => lazymatch x with Some _ => idtac | None => idtac end;
                       lazymatch y with Some _ => idtac | None => idtac end;
                       progress cbn [option_eq]
                  | [ |- UnderLets.wf _ _ (Reify.expr_value_to_rewrite_rule_replacement ?rii1 ?sda _) (Reify.expr_value_to_rewrite_rule_replacement ?rii2 ?sda _) ]
                    => apply (fun H => @Reify.wf_expr_value_to_rewrite_rule_replacement _ _ _ rii1 rii2 H sda); intros
                  | [ |- option_eq _ (Compile.reflect_ident_iota _) (Compile.reflect_ident_iota _) ]
                    => apply Reify.wf_reflect_ident_iota
                  | [ |- ?x = ?x ] => reflexivity
                  end
                | break_innermost_match_step
                | progress cbv [Compile.wf_maybe_do_again_expr] in *
                | progress fin_wf ].

      Ltac handle_extra_nbe :=
        repeat first [ match goal with
                       | [ |- expr.wf _ (reify_list _) (reify_list _) ] => rewrite expr.wf_reify_list
                       | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
                       | [ |- List.Forall2 _ (List.map _ _) (List.map _ _) ] => rewrite Forall2_map_map_iff
                       | [ |- List.Forall _ (seq _ _) ] => rewrite Forall_seq
                       end
                     | progress intros
                     | progress fin_wf ].

      Ltac handle_extra_arith_rules :=
        repeat first [ progress cbv [option_eq SubstVarLike.is_var_fst_snd_pair_opp_cast] in *
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
          do_time start_good;
          do_time ltac:(fun _ => handle_reified_rewrite_rules; handle_extra_nbe; handle_extra_arith_rules).
      End Tactic.
    End WfTactics.

    Module InterpTactics.
      Import Crypto.Util.ZRange.
      Export RewriterWf1.Compilers.RewriteRules.InterpTactics.

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
        | [ |- context[@Interp_GoalT ?pkg] ]
          => let pkg' := (eval hnf in pkg) in
             replace pkg with pkg' by reflexivity
        end;
        cbv [List.skipn Interp_GoalT] in *; Compilers.pattern.ident.GoalType.red_proj; intros;
        lazymatch goal with
        | [ |- @Compile.rewrite_rules_interp_goodT ?ident ?pident ?pident_arg_types ?pident_to_typed ?ident_interp (Make.GoalType.rewrite_rules ?data ?var) ]
          => let H := fresh in
             pose proof (@Compile.rewrite_rules_interp_goodT_by_curried
                           ident pident pident_arg_types pident_to_typed ident_interp (Make.GoalType.rewrite_rules data var) (rewrite_rules_specs data)) as H;
             let data' := (eval hnf in data) in
             change data with data' in * |- ;
             cbv [Make.GoalType.rewrite_rules dummy_count rewrite_rules_specs] in * |- ;
             let h' := lazymatch type of H with context[Compile.rewrite_rules_interp_goodT_curried_cps _ _ _ ?v] => head v end in
             unfold h' in H at 1;
             let pident_arg_types' := (eval cbv -[base.interp] in pident_arg_types) in
             change pident_arg_types with pident_arg_types' in H;
             let pident_to_typed' := (eval cbv -[pattern.type.subst_default pattern.base.subst_default List.fold_right base.interp base.base_interp Datatypes.fst Datatypes.snd] in pident_to_typed) in
             let pident_to_typed' := (eval cbn [Datatypes.fst Datatypes.snd List.fold_right] in pident_to_typed') in
             change pident_to_typed with pident_to_typed' in H;
             cbv [Compile.rewrite_rules_interp_goodT_curried_cps] in H;
             cbn [snd hd tl projT1 projT2] in H;
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
          cbn [fst snd base.interp base.base_interp type.interp projT1 projT2 UnderLets.interp expr.interp type.related ident.gen_interp] in *;
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
                                 .. ].

      Ltac recurse_interp_related_step :=
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
             cbn [expr.interp_related_gen]; apply ident.gen_interp_Proper; reflexivity
        | [ |- _ = _ :> ?T ]
          => lazymatch T with
             | BinInt.Z => idtac
             | (BinInt.Z * BinInt.Z)%type => idtac
             end;
             progress cbn [ident.gen_interp fst snd]
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

      Ltac preprocess_step :=
        first [ progress cbv [expr.interp_related respectful ident.literal ident.eagerly] in *
              | progress cbn [fst snd base.interp base.base_interp Compile.value'] in *
              | progress intros
              | progress subst
              | match goal with
                | [ |- context[match _ with nil => _ | _ => _ end] ] => progress recursive_match_to_case_in_goal
                | [ |- context[match _ with pair a b => _ end] ] => progress recursive_match_to_case_in_goal
                | [ |- context[match _ with true => _ | false => _ end] ] => progress recursive_match_to_case_in_goal
                | [ |- context[match invert_expr.reflect_list ?ls with _ => _ end] ]
                  => destruct (invert_expr.reflect_list ls) eqn:?
                | [ |- context G[expr.interp_related_gen ?ident_interp (fun t : ?T => ?vii t ?b)] ]
                  => progress change (fun t : T => vii t b) with (fun t : T => @Compile.value_interp_related _ ident_interp t b)
                end ].
      Ltac preprocess := repeat preprocess_step.
      Ltac handle_extra_nbe :=
        repeat match goal with
               | [ |- UnderLets.interp_related _ _ (UnderLets.Base (expr.Ident _)) _ ]
                 => cbn [UnderLets.interp_related UnderLets.interp_related_gen expr.interp_related_gen ident.gen_interp type.related]; reflexivity
               | [ |- UnderLets.interp_related _ _ (UnderLets.Base (reify_list _)) _ ]
                 => cbn [UnderLets.interp_related UnderLets.interp_related_gen]; rewrite expr.reify_list_interp_related_gen_iff
               | [ |- UnderLets.interp_related _ _ (UnderLets.Base (_, _)%expr) ?x ]
                 => cbn [UnderLets.interp_related UnderLets.interp_related_gen];
                    recurse_interp_related_step;
                    [ recurse_interp_related_step
                    | lazymatch x with
                      | (_, _) => reflexivity
                      | _ => etransitivity; [ | symmetry; apply surjective_pairing ]; reflexivity
                      end ];
                    [ | reflexivity ]; cbn [fst snd];
                    recurse_interp_related_step; [ recurse_interp_related_step | reflexivity ]
               | [ |- List.Forall2 _ (List.map _ _) _ ]
                 => rewrite Forall2_map_l_iff
               | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
               | [ |- List.Forall _ _ ] => rewrite Forall_forall; intros
               | [ |- expr.interp_related_gen _ _ (expr.Ident _) _ ]
                 => cbn [expr.interp_related_gen ident.gen_interp type.related]; reflexivity
               end.
      Ltac fin_tac :=
        repeat first [ assumption
                     | progress change S with Nat.succ
                     | progress cbn [base.interp base.base_interp type.interp] in *
                     | progress fold (@type.interp _ base.interp)
                     | progress fold (@base.interp)
                     | progress subst
                     | progress cbv [respectful ident.Thunked.bool_rect ident.Thunked.list_case ident.Thunked.option_rect pointwise_relation]
                     | progress intros
                     | solve [ auto ]
                     | match goal with
                       | [ |- ?x = ?x ] => reflexivity
                       | [ |- list_rect _ _ _ _ = ident.Thunked.list_rect _ _ _ _ ]
                         => cbv [ident.Thunked.list_rect]; apply list_rect_Proper; cbv [pointwise_relation]; intros
                       | [ |- list_rect (fun _ => ?A -> ?B) _ _ _ _ = list_rect _ _ _ _ _ ]
                         => apply list_rect_arrow_Proper; cbv [respectful]; intros
                       | [ |- nat_rect _ _ _ _ = ident.Thunked.nat_rect _ _ _ _ ]
                         => apply nat_rect_Proper_nondep; cbv [respectful]
                       | [ |- nat_rect (fun _ => ?A -> ?B) _ _ _ _ = nat_rect _ _ _ _ _ ]
                         => apply (@nat_rect_Proper_nondep_gen (A -> B) (eq ==> eq)%signature); cbv [respectful]; intros
                       | [ |- list_case _ _ _ ?ls = list_case _ _ _ ?ls ]
                         => is_var ls; destruct ls; cbn [list_case]
                       | [ |- bool_rect _ _ _ ?b = bool_rect _ _ _ ?b ]
                         => is_var b; destruct b; cbn [bool_rect]
                       | [ |- _ = ident.cast2 _ _ _ ] => cbv [ident.cast2]; break_innermost_match
                       end ].
      Ltac handle_reified_rewrite_rules_interp :=
        repeat first [ assumption
                     | match goal with
                       | [ cast_outside_of_range : zrange -> Z -> Z |- UnderLets.interp_related _ _ (Reify.expr_value_to_rewrite_rule_replacement _ ?sda _) _ ]
                         => apply (@Reify.expr_value_to_rewrite_rule_replacement_interp_related cast_outside_of_range _ (@Reify.reflect_ident_iota_interp_related cast_outside_of_range) sda)

                       | [ |- UnderLets.interp_related_gen ?ii ?R (UnderLets.Base (#ident.list_rect @ _ @ _ @ _)%expr) (@list_rect ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => progress change (@list_rect A (fun _ => P) N C ls) with (@ident.Thunked.list_rect A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.list_rect @ _ @ _ @ _)%expr (@list_rect ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => progress change (@list_rect A (fun _ => P) N C ls) with (@ident.Thunked.list_rect A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.eager_list_rect @ _ @ _ @ _)%expr (@list_rect ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => progress change (@list_rect A (fun _ => P) N C ls) with (@ident.Thunked.list_rect A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.list_case @ _ @ _ @ _)%expr (@list_case ?A (fun _ => ?P) ?N ?C ?ls) ]
                         => progress change (@list_case A (fun _ => P) N C ls) with (@ident.Thunked.list_case A P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.nat_rect @ _ @ _ @ _)%expr (@nat_rect (fun _ => ?P) ?N ?C ?ls) ]
                         => progress change (@nat_rect (fun _ => P) N C ls) with (@ident.Thunked.nat_rect P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.eager_nat_rect @ _ @ _ @ _)%expr (@nat_rect (fun _ => ?P) ?N ?C ?ls) ]
                         => progress change (@nat_rect (fun _ => P) N C ls) with (@ident.Thunked.nat_rect P (fun _ => N) C ls)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.bool_rect @ _ @ _ @ _)%expr (@bool_rect (fun _ => ?P) ?T ?F ?b) ]
                         => progress change (@bool_rect (fun _ => P) T F b) with (@ident.Thunked.bool_rect P (fun _ => T) (fun _ => F) b)
                       | [ |- expr.interp_related_gen ?ii ?R (#ident.option_rect @ _ @ _ @ _)%expr (@option_rect ?A (fun _ => ?P) ?S ?N ?o) ]
                         => progress change (@option_rect A (fun _ => P) S N o) with (@ident.Thunked.option_rect A P S (fun _ => N) o)

                       | [ |- match ?x with pair _ _ => _ end = prod_rect _ _ _ ]
                         => cbv [prod_rect]; eta_expand

                       | [ |- expr.interp_related_gen _ _ (expr.Var _) _ ]
                         => cbn [expr.interp_related_gen]
                       | [ |- expr.interp_related_gen _ _ (expr.Ident _) _ ]
                         => cbn [expr.interp_related_gen ident.gen_interp type.related]; fin_tac
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
                       | [ |- type.eqv _ _ ] => cbn [ident.gen_interp type.related]; cbv [respectful]; intros; subst
                       end
                     | progress repeat (do 2 eexists; repeat apply conj; [ | | reflexivity ]) ].

      Module Export Tactic.
        Ltac prove_interp_good _ :=
          let do_time := Make.time_if_debug1 in (* eval the level early *)
          do_time start_interp_good;
          do_time ltac:(fun _ => preprocess; handle_extra_nbe; handle_reified_rewrite_rules_interp).
      End Tactic.
    End InterpTactics.
  End RewriteRules.
End Compilers.
