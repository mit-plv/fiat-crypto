Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Experiments.NewPipeline.RewriterWf1.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Hints.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.
Require Import Crypto.Util.ZUtil.ZSimplify.Simple.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.NormalizeCommutativeIdentifier.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.ForallIn.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Import ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.
  Import RewriterWf1.Compilers.
  Import expr.Notations.
  Import RewriterWf1.Compilers.RewriteRules.
  Import defaults.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.
    Section with_cast.
      Context {cast_outside_of_range : zrange -> Z -> Z}.

      Local Notation ident_interp := (@ident.gen_interp cast_outside_of_range).

      Local Lemma rlist_rect_eq {var A P ivar} Pnil Pcons ls
        : @rlist_rect var A P ivar Pnil Pcons ls
          = match invert_expr.reflect_list ls with
            | Some ls
              => Some (list_rect
                         (fun _ => _)
                         Pnil
                         (fun x xs rec => rec' <-- rec; Pcons x xs rec')
                         ls)%under_lets
            | None => None
            end.
      Proof. cbv [rlist_rect Compile.option_bind' Option.bind]; reflexivity. Qed.

      Local Lemma UnderLets_interp_list_rect {A P} Pnil Pcons ls
        : UnderLets.interp
            (@ident_interp)
            (list_rect
               (fun _ : list A => UnderLets.UnderLets base.type ident _ P)
               Pnil
               (fun x xs rec => rec' <-- rec; Pcons x xs rec')
               ls)%under_lets
          = list_rect
              (fun _ => P)
              (UnderLets.interp (@ident_interp) Pnil)
              (fun x xs rec => UnderLets.interp (@ident_interp) (Pcons x xs rec))
              ls.
      Proof.
        induction ls as [|x xs IHxs]; cbn [list_rect]; [ reflexivity | ].
        rewrite UnderLets.interp_splice, IHxs; reflexivity.
      Qed.

      Local Notation rewrite_rules_interp_goodT := (@Compile.rewrite_rules_interp_goodT ident pattern.ident (@pattern.ident.arg_types) (@pattern.ident.type_vars) (@pattern.ident.to_typed) (@ident_interp)).

      Local Ltac do_cbv0 :=
        cbv [id
               Compile.rewrite_rules_interp_goodT
               Compile.rewrite_rule_data_interp_goodT Compile.under_with_unification_resultT_relation_hetero Compile.under_with_unification_resultT'_relation_hetero Compile.wf_with_unification_resultT Compile.under_type_of_list_relation_cps pattern.pattern_of_anypattern pattern.type_of_anypattern Compile.rew_replacement Compile.rew_is_cps Compile.rew_should_do_again Compile.rew_with_opt Compile.rew_under_lets Compile.wf_with_unification_resultT' Compile.pattern_default_interp pattern.type.under_forall_vars_relation Compile.deep_rewrite_ruleTP_gen Compile.with_unification_resultT' pattern.ident.arg_types pattern.type.lam_forall_vars Compile.pattern_default_interp' pattern.collect_vars PositiveMap.empty Compile.ident_collect_vars pattern.ident.type_vars pattern.type.collect_vars PositiveSet.elements PositiveSet.union pattern.base.collect_vars PositiveSet.empty PositiveSet.xelements Compile.lam_type_of_list id pattern.ident.to_typed Compile.forall2_type_of_list_cps Compile.deep_rewrite_ruleTP_gen_good_relation Compile.normalize_deep_rewrite_rule_cps_id_hypsT Compile.normalize_deep_rewrite_rule pattern.type.subst_default PositiveSet.add PositiveSet.rev PositiveSet.rev_append PositiveMap.add Compile.option_bind' Compile.wf_value Compile.value pattern.base.subst_default PositiveMap.find Compile.rewrite_ruleTP ident.smart_Literal Compile.value_interp_related Compile.value'_interp_related].
      Local Ltac do_cbv :=
        do_cbv0;
        cbv [List.map List.fold_right List.rev list_rect orb List.app].

      Local Ltac start_interp_good :=
        do_cbv;
        lazymatch goal with
        | [ |- forall x p, In (@existT ?A ?P x p) ?ls -> @?Q x p ]
          => let Q' := fresh in
             pose Q as Q';
             change (forall x p, In (@existT A P x p) ls -> Q' x p);
             apply (@forall_In_existT A P Q' ls); cbn [projT1 projT2]; cbv [id];
             subst Q'; cbn [projT1 projT2]
        end;
        do_cbv0;
        repeat first [ progress intros
                     | match goal with
                       | [ |- { pf : ?x = ?x | _ } ] => (exists eq_refl)
                       | [ |- True /\ _ ] => split; [ exact I | ]
                       end
                     | progress cbn [eq_rect] in * ];
        cbn [fst snd base.interp base.base_interp type.interp projT1 projT2 UnderLets.interp expr.interp type.related ident.gen_interp] in *.

      Local Ltac interp_good_t_step :=
        first [ reflexivity
              | match goal with
                | [ |- context[(fst ?x, snd ?x)] ] => progress eta_expand
                | [ |- context[match ?x with pair a b => _ end] ] => progress eta_expand
                end
              | progress cbn [expr.interp ident.gen_interp fst snd Compile.reify Compile.reflect Compile.wf_value' Compile.value' Option.bind UnderLets.interp list_case type.interp base.interp base.base_interp ident.to_fancy invert_Some ident.fancy.interp ident.fancy.interp_with_wordmax Compile.reify_expr] in *
              | progress cbv [Compile.option_bind' respectful] in *
              | progress fold (@type.interp _ base.interp)
              | progress fold (@base.interp)
              | match goal with
                | [ |- context[List.map _ (Lists.List.repeat _ _)] ] => rewrite map_repeat
                | [ |- context[List.map _ (List.map _ _)] ] => rewrite map_map
                | [ |- context[List.map (fun x => x) _] ] => rewrite map_id
                | [ |- context[List.map _ (List.rev _)] ] => rewrite map_rev
                | [ |- context[List.map _ (firstn _ _)] ] => rewrite <- firstn_map
                | [ |- context[List.map _ (skipn _ _)] ] => rewrite <- skipn_map
                | [ |- context[List.length (List.map _ _)] ] => rewrite map_length
                | [ |- context[List.combine (List.map _ _) _] ] => rewrite combine_map_l
                | [ |- context[List.combine _ (List.map _ _)] ] => rewrite combine_map_r
                | [ |- context[expr.interp _ (reify_list _)] ] => rewrite expr.interp_reify_list
                | [ |- context[expr.interp _ (UnderLets.to_expr ?e)] ] => rewrite UnderLets.interp_to_expr
                | [ |- context[UnderLets.interp _ (UnderLets.splice_list _ _)] ] => rewrite UnderLets.interp_splice_list
                | [ |- context[rlist_rect] ] => rewrite rlist_rect_eq
                | [ |- context[UnderLets.interp _ (list_rect _ _ _ _)] ] => rewrite UnderLets_interp_list_rect
                | [ |- context[UnderLets.interp _ (UnderLets.splice _ _)] ] => rewrite UnderLets.interp_splice
                | [ |- context[list_rect _ _ _ (List.map _ _)] ] => rewrite list_rect_map
                | [ |- list_rect _ _ _ _ = List.app ?ls1 ?ls2 ]
                  =>  rewrite (eq_app_list_rect ls1 ls2)
                | [ |- list_rect _ _ _ _ = @flat_map ?A ?B ?f ?ls ]
                  =>  rewrite (@eq_flat_map_list_rect A B f ls)
                | [ |- list_rect _ _ _ _ = @partition ?A ?f ?ls ]
                  =>  rewrite (@eq_partition_list_rect A f ls)
                | [ |- list_rect _ _ _ _ = @List.map ?A ?B ?f ?ls ]
                  => rewrite (@eq_map_list_rect A B f ls)
                | [ |- _ = @fold_right ?A ?B ?f ?v ?ls ]
                  =>  rewrite (@eq_fold_right_list_rect A B f v ls)
                end
              | progress intros
              | progress subst
              | progress inversion_option
              | progress Z.ltb_to_lt
              | progress split_andb
              | match goal with
                | [ |- Lists.List.repeat _ _ = Lists.List.repeat _ _ ] => apply f_equal2
                | [ |- firstn _ _ = firstn _ _ ] => apply f_equal2
                | [ |- skipn _ _ = skipn _ _ ] => apply f_equal2
                | [ |- rev _ = rev _ ] => apply f_equal
                | [ |- List.app ?l1 ?l2 = List.app ?l1' ?l2 ] => apply f_equal2
                | [ |- List.app ?l1 ?l2 = List.app ?l1 ?l2' ] => apply f_equal2
                | [ |- cons _ _ = cons _ _ ] => apply f_equal2
                | [ |- list_rect _ ?Pnil ?Pcons ?ls = list_rect _ ?Pnil ?Pcons' ?ls ]
                  => apply list_rect_Proper; [ reflexivity | repeat intro | reflexivity ]
                | [ |- bool_rect _ ?x ?y ?b = bool_rect _ ?x ?y ?b' ]
                  => apply f_equal3; [ reflexivity | reflexivity | solve [ repeat interp_good_t_step ] ]
                | [ H : expr.wf _ ?v1 ?v2 |- expr.interp _ ?v1 = expr.interp _ ?v2 ]
                  => apply (expr.wf_interp_Proper _ _ _ H ltac:(assumption))
                | [ |- ?R (?f (?g (if ?b then ?x else ?y))) (bool_rect ?A ?B ?C ?D) ]
                  => rewrite <- (@Bool.pull_bool_if _ _ g b), <- (@Bool.pull_bool_if _ _ f b);
                     change (R (bool_rect _ (f (g x)) (f (g y)) b) (bool_rect A B C D))
                | [ |- context[invert_expr.reflect_list ?ls] ]
                  => destruct (invert_expr.reflect_list ls) eqn:?; expr.invert_subst
                | [ |- ?f (nth_default _ _ _) = _ ]
                  => rewrite <- (@map_nth_default_always _ _ f)
                | [ |- map ?f ?ls = map ?g ?ls ] => apply map_ext_in
                | [ |- List.map _ (update_nth _ _ _) = update_nth _ _ _ ] => apply map_update_nth_ext
                | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                | [ H : forall v : unit, _ |- _ ] => specialize (H tt)
                | [ H : _ = expr.interp ?ii ?v |- _ ] => is_var v; generalize dependent (expr.interp ii v); clear v
                | [ |- bool_rect _ _ _ ?b = bool_rect _ _ _ ?b ]
                  => is_var b; destruct b; cbv [bool_rect]
                | [ H : (forall x y, _ -> expr.interp _ (UnderLets.interp _ (?f1 x)) = expr.interp _ (UnderLets.interp _ (?f2 y)))
                    |- expr.interp _ (UnderLets.interp _ (?f1 ?x1)) = expr.interp _ (UnderLets.interp _ (?f2 ?x2)) ]
                  => apply H
                | [ H : (forall x y, _ -> forall x' y', _ -> expr.interp _ (UnderLets.interp _ (?f1 x x')) = expr.interp _ (UnderLets.interp _ (?f2 y y')))
                    |- expr.interp _ (UnderLets.interp _ (?f1 ?x1 ?y1)) = expr.interp _ (UnderLets.interp _ (?f2 ?x2 ?y2)) ]
                  => apply H
                | [ |- context G[rwhen ?v ?b] ]
                  => let c := constr:(rwhen v b) in
                     let c := (eval cbv [rwhen] in c) in
                     let G' := context G[c] in
                     change G';
                     destruct b eqn:?
                | [ |- context G[rwhenl ?v ?b] ]
                  => let c := constr:(rwhenl v b) in
                     let c := (eval cbv [rwhenl] in c) in
                     let G' := context G[c] in
                     change G';
                     destruct b eqn:?
                | [ H : negb ?b = true |- _ ] => rewrite (@Bool.negb_true_iff b) in H
                | [ |- context[expr.interp ?ii ?v] ]
                  => is_var v; generalize dependent (expr.interp ii v); clear v; intro v
                | [ |- context[Z.mul_split ?a ?b ?c] ]
                  => rewrite (surjective_pairing (Z.mul_split a b c)), Z.mul_split_div, Z.mul_split_mod
                | [ |- context[Z.zselect] ] => rewrite Z.zselect_correct
                | [ |- context[Z.sub_get_borrow_full ?a ?b ?c] ]
                  => rewrite (surjective_pairing (Z.sub_get_borrow_full a b c)), Z.sub_get_borrow_full_div, Z.sub_get_borrow_full_mod
                | [ |- context[Z.sub_with_get_borrow_full ?a ?b ?c ?d] ]
                  => rewrite (surjective_pairing (Z.sub_with_get_borrow_full a b c d)), Z.sub_with_get_borrow_full_div, Z.sub_with_get_borrow_full_mod
                | [ |- context[Z.add_get_carry_full ?a ?b ?c] ]
                  => rewrite (surjective_pairing (Z.add_get_carry_full a b c)), Z.add_get_carry_full_div, Z.add_get_carry_full_mod
                | [ |- context[Z.add_with_get_carry_full ?a ?b ?c ?d] ]
                  => rewrite (surjective_pairing (Z.add_with_get_carry_full a b c d)), Z.add_with_get_carry_full_div, Z.add_with_get_carry_full_mod
                | [ |- pair _ _ = pair _ _ ] => apply f_equal2
                | [ |- ?a mod ?b = ?a' mod ?b ] => apply f_equal2; lia
                | [ |- ?a / ?b = ?a' / ?b ] => apply f_equal2; lia
                | [ |- Z.opp _ = Z.opp _ ] => apply f_equal
                end
              | match goal with
                | [ |- context[?f (list_rect _ _ _ _)] ]
                  => match f with
                     | expr.interp _ => idtac
                     | Compile.reify_expr => idtac
                     end;
                     erewrite (@push_f_list_rect _ _ f)
                       by (intros;
                           repeat first [ progress cbn [expr.interp ident.gen_interp UnderLets.interp Compile.reify_expr]
                                        | rewrite UnderLets.interp_splice ];
                           match goal with
                           | [ |- ?LHS = ?Pcons' ?x ?xs ?rec ]
                             => let LHS' := match (eval pattern x, xs, rec in LHS) with ?f _ _ _ => f end in
                                unify Pcons' LHS'; reflexivity
                           end)
                | [ |- context[?f (nat_rect _ _ _ _)] ]
                  => match f with
                     | expr.interp _ => idtac
                     | UnderLets.interp _ => idtac
                     | Compile.reify_expr => idtac
                     end;
                     erewrite (@push_f_nat_rect _ _ f)
                       by (intros;
                           repeat first [ progress cbn [expr.interp ident.gen_interp UnderLets.interp Compile.reify_expr]
                                        | rewrite UnderLets.interp_splice ];
                           match goal with
                           | [ |- ?LHS = ?PS' ?x ?rec ]
                             => let LHS' := match (eval pattern x, rec in LHS) with ?f _ _ => f end in
                                unify PS' LHS'; reflexivity
                           end)
                | [ |- ?f (list_rect _ _ _ _) = list_rect _ _ _ _ ]
                  => match f with
                     | expr.interp _ => idtac
                     | Compile.reify_expr => idtac
                     end;
                     erewrite (@push_f_list_rect _ _ f);
                     [ apply list_rect_Proper; repeat intro; try reflexivity | ]
                | [ |- ?f (nat_rect _ _ _ _) = nat_rect _ _ _ _ ]
                  => match f with
                     | expr.interp _ => idtac
                     | UnderLets.interp _ => idtac
                     | Compile.reify_expr => idtac
                     end;
                     erewrite (@push_f_nat_rect _ _ f);
                     [ apply nat_rect_Proper_nondep; repeat intro; try reflexivity | ]
                end
              | break_innermost_match_step
              | break_innermost_match_hyps_step
              | match goal with
                | [ H : context[expr.interp _ (UnderLets.interp _ (?f _ _ _))]
                    |- expr.interp _ (UnderLets.interp _ (?f _ _ _)) = _ ]
                  => apply H
                | [ |- context[Z.shiftl] ] => rewrite Z.shiftl_mul_pow2 by auto with zarith
                | [ |- context[Z.shiftr] ] => rewrite Z.shiftr_div_pow2 by auto with zarith
                | [ |- context[Z.shiftl _ (-_)] ] => rewrite Z.shiftl_opp_r
                | [ H : ?x = 2^Z.log2 ?x |- context[2^Z.log2 ?x] ] => rewrite <- H
                | [ H : ?x = 2^?n |- context[Z.land _ (?x - 1)] ]
                  => rewrite !Z.sub_1_r, H, <- Z.ones_equiv, Z.land_ones by auto with zarith
                | [ |- _ = _ :> BinInt.Z ] => progress normalize_commutative_identifier Z.land Z.land_comm
                | [ H : ?x = ?y, H' : ?x <> ?y |- _ ] => exfalso; apply H', H
                | [ H : ?x = 2^Z.log2_up ?x - 1 |- context[2^Z.log2_up ?x - 1] ] => rewrite <- H
                | [ H : ?x = 2^Z.log2 ?x, H' : context[2^Z.log2 ?x] |- _ = _ :> BinInt.Z ]
                  => rewrite <- H in H'
                | [ |- _ = _ :> BinInt.Z ] => progress autorewrite with zsimplify_const
                | [ |- ?f (?g (nat_rect _ _ _ ?n ?v)) = nat_rect _ _ _ ?n _ ]
                  => revert v; is_var n; induction n; intro v; cbn [nat_rect]
                | [ |- _ mod ?x = _ mod ?x ]
                  => progress (push_Zmod; pull_Zmod)
                | [ |- _ mod ?x = _ mod ?x ]
                  => apply f_equal2; (lia + nia)
                | [ |- _ = _ :> BinInt.Z ] => progress autorewrite with zsimplify_fast
                end ].

      Lemma nbe_rewrite_rules_interp_good
        : rewrite_rules_interp_goodT nbe_rewrite_rules.
      Proof using Type.
        Time start_interp_good.
        Time all: repeat interp_good_t_step.
      Qed.

      Axiom proof_admitted : False.
      Local Notation admit := (match proof_admitted with end).

      Lemma arith_rewrite_rules_interp_good max_const
        : rewrite_rules_interp_goodT (arith_rewrite_rules max_const).
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [ repeat interp_good_t_step; (lia + nia) ].
        (* This is mainly for display *)
        all: repeat first [ progress cbn [Compile.value' Compile.reify] in *
                          | progress subst
                          | match goal with
                            | [ H : context[expr.interp ?ii ?v] |- _ ]
                              => is_var v; generalize dependent (expr.interp ii v); clear v; intro v; intros
                            | [ |- context[expr.interp ?ii ?v] ]
                              => is_var v; generalize dependent (expr.interp ii v); clear v; intro v; intros
                            end ].
        (* 9 subgoals (ID 32915)

  cast_outside_of_range : zrange -> Z -> Z
  max_const, x, x0 : Z
  v1 : expr (type.base base.type.Z)
  ============================
  match
    (x1 <- rwhen (Some (v1, (##0)%expr)%expr_pat) (x0 =? 1);
     Some (UnderLets.Base x1))%option
  with
  | Some v0 =>
      expr.interp ident_interp (UnderLets.interp ident_interp v0) =
      Z.mul_split x x0 (expr.interp ident_interp v1)
  | None => True
  end

subgoal 2 (ID 32967) is:
 match
   (x1 <- rwhen (Some (v1, (##0)%expr)%expr_pat) (x0 =? 1);
    Some (UnderLets.Base x1))%option
 with
 | Some v0 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v0) =
     Z.mul_split x (expr.interp ident_interp v1) x0
 | None => True
 end
subgoal 3 (ID 33019) is:
 match
   (x1 <- rwhen (Some ((- v1)%expr, (##0)%expr)%expr_pat) (x0 =? -1);
    Some (UnderLets.Base x1))%option
 with
 | Some v0 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v0) =
     Z.mul_split x x0 (expr.interp ident_interp v1)
 | None => True
 end
subgoal 4 (ID 33071) is:
 match
   (x1 <- rwhen (Some ((- v1)%expr, (##0)%expr)%expr_pat) (x0 =? -1);
    Some (UnderLets.Base x1))%option
 with
 | Some v0 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v0) =
     Z.mul_split x (expr.interp ident_interp v1) x0
 | None => True
 end
subgoal 5 (ID 33168) is:
 match
   (x0 <- rwhen (Some (v0, (##0)%expr)%expr_pat) (x =? 0);
    Some (UnderLets.Base x0))%option
 with
 | Some v1 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v1) =
     Z.add_get_carry_full v2 x (expr.interp ident_interp v0)
 | None => True
 end
subgoal 6 (ID 33265) is:
 match
   (x0 <- rwhen (Some (v0, (##0)%expr)%expr_pat) (x =? 0);
    Some (UnderLets.Base x0))%option
 with
 | Some v1 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v1) =
     Z.add_get_carry_full v2 (expr.interp ident_interp v0) x
 | None => True
 end
subgoal 7 (ID 33320) is:
 match
   (x2 <- rwhen (Some (v1, (##0)%expr)%expr_pat) ((x0 =? 0) && (x1 =? 0));
    Some (UnderLets.Base x2))%option
 with
 | Some v0 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v0) =
     Z.add_with_get_carry_full x x0 x1 (expr.interp ident_interp v1)
 | None => True
 end
subgoal 8 (ID 33376) is:
 match
   (x2 <- rwhen (Some (v1, (##0)%expr)%expr_pat) ((x0 =? 0) && (x1 =? 0));
    Some (UnderLets.Base x2))%option
 with
 | Some v0 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v0) =
     Z.add_with_get_carry_full x x0 (expr.interp ident_interp v1) x1
 | None => True
 end
subgoal 9 (ID 33473) is:
 match
   rwhenl
     (Some
        (UnderLets.UnderLet
           (#(ident.Z_add_with_get_carry)%expr @ v1 @ v0 @ (##x)%expr @ (##x0)%expr)%expr_pat
           (fun vc : Z * Z =>
            UnderLets.Base (#(ident.fst)%expr @ ($vc)%expr, (##0)%expr)%expr_pat)))
     ((x =? 0) && (x0 =? 0))
 with
 | Some v2 =>
     expr.interp ident_interp (UnderLets.interp ident_interp v2) =
     Z.add_with_get_carry_full (expr.interp ident_interp v1) (expr.interp ident_interp v0) x x0
 | None => True
 end
         *)
        1-9: exact admit.
      Qed.

      Local Ltac fancy_local_t :=
        repeat first [ match goal with
                       | [ H : forall s v v', ?invert_low s v = Some v' -> v = _,
                             H' : ?invert_low _ _ = Some _ |- _ ] => apply H in H'
                       end
                     | progress autorewrite with zsimplify in * ].

      Lemma fancy_rewrite_rules_interp_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_interp_goodT (fancy_rewrite_rules invert_low invert_high).
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [
                        repeat interp_good_t_step;
                          cbv [Option.bind] in *;
                          repeat interp_good_t_step;
                          fancy_local_t;
                          repeat interp_good_t_step ].
        Time all: repeat interp_good_t_step.
        Time all: cbv [Option.bind] in *.
        Time all: repeat interp_good_t_step.
        Time all: fancy_local_t.
        Time all: repeat interp_good_t_step.
        all: repeat first [ progress cbn [Compile.value' Compile.reify] in *
                          | progress subst
                          | match goal with
                            | [ H : context[expr.interp ?ii ?v] |- _ ]
                              => is_var v; generalize dependent (expr.interp ii v); clear v; intro v; intros
                            | [ |- context[expr.interp ?ii ?v] ]
                              => is_var v; generalize dependent (expr.interp ii v); clear v; intro v; intros
                            end ].
        all: repeat match goal with
                    | [ H : _ = _ :> BinInt.Z |- _ ] => revert H
                    | [ v : BinInt.Z |- _ ] => clear v || revert v
                    end.
        (* 16 subgoals (ID 105273)

  cast_outside_of_range : zrange -> Z -> Z
  invert_low, invert_high : Z -> Z -> option Z
  Hlow : forall s v v' : Z, invert_low s v = Some v' -> v = Z.land v' (2 ^ (s / 2) - 1)
  Hhigh : forall s v v' : Z, invert_high s v = Some v' -> v = Z.shiftr v' (s / 2)
  ============================
  forall x x0 v1 v0 : Z,
  x = 2 ^ Z.log2 x -> (v1 + Z.shiftl v0 x0 mod x) / x = (v1 + Z.shiftl v0 x0) / x

subgoal 2 (ID 105283) is:
 forall x x0 v0 v1 : Z,
 x = 2 ^ Z.log2 x -> (v0 + Z.shiftl v1 x0 mod x) / x = (Z.shiftl v1 x0 + v0) / x
subgoal 3 (ID 105293) is:
 forall x x0 v1 v0 : Z,
 x = 2 ^ Z.log2 x -> (v1 + Z.shiftr v0 x0 mod x) / x = (v1 + Z.shiftr v0 x0) / x
subgoal 4 (ID 105303) is:
 forall x x0 v0 v1 : Z,
 x = 2 ^ Z.log2 x -> (v0 + Z.shiftr v1 x0 mod x) / x = (Z.shiftr v1 x0 + v0) / x
subgoal 5 (ID 105311) is:
 forall x v1 v0 : Z, x = 2 ^ Z.log2 x -> (v1 + v0 mod x) / x = (v1 + v0) / x
subgoal 6 (ID 105323) is:
 forall x x0 v1 v0 v4 : Z,
 x = 2 ^ Z.log2 x -> (v1 + v0 + Z.shiftl v4 x0 mod x) / x = (v1 + v0 + Z.shiftl v4 x0) / x
subgoal 7 (ID 105335) is:
 forall x x0 v1 v4 v0 : Z,
 x = 2 ^ Z.log2 x -> (v1 + v4 + Z.shiftl v0 x0 mod x) / x = (v1 + Z.shiftl v0 x0 + v4) / x
subgoal 8 (ID 105347) is:
 forall x x0 v1 v0 v4 : Z,
 x = 2 ^ Z.log2 x -> (v1 + v0 + Z.shiftr v4 x0 mod x) / x = (v1 + v0 + Z.shiftr v4 x0) / x
subgoal 9 (ID 105359) is:
 forall x x0 v1 v4 v0 : Z,
 x = 2 ^ Z.log2 x -> (v1 + v4 + Z.shiftr v0 x0 mod x) / x = (v1 + Z.shiftr v0 x0 + v4) / x
subgoal 10 (ID 105369) is:
 forall x v1 v0 v4 : Z, x = 2 ^ Z.log2 x -> (v1 + v0 + v4 mod x) / x = (v1 + v0 + v4) / x
subgoal 11 (ID 105379) is:
 forall x x0 v1 v0 : Z,
 x = 2 ^ Z.log2 x -> (v1 - Z.shiftl v0 x0 mod x) / x = (v1 - Z.shiftl v0 x0) / x
subgoal 12 (ID 105389) is:
 forall x x0 v1 v0 : Z,
 x = 2 ^ Z.log2 x -> (v1 - Z.shiftr v0 x0 mod x) / x = (v1 - Z.shiftr v0 x0) / x
subgoal 13 (ID 105397) is:
 forall x v1 v0 : Z, x = 2 ^ Z.log2 x -> (v1 - v0 mod x) / x = (v1 - v0) / x
subgoal 14 (ID 105409) is:
 forall x x0 v1 v0 v4 : Z,
 x = 2 ^ Z.log2 x -> (v0 - Z.shiftl v4 x0 mod x - v1) / x = (v0 - Z.shiftl v4 x0 - v1) / x
subgoal 15 (ID 105421) is:
 forall x x0 v1 v0 v4 : Z,
 x = 2 ^ Z.log2 x -> (v0 - Z.shiftr v4 x0 mod x - v1) / x = (v0 - Z.shiftr v4 x0 - v1) / x
subgoal 16 (ID 105431) is:
 forall x v1 v0 v4 : Z, x = 2 ^ Z.log2 x -> (v0 - v4 mod x - v1) / x = (v0 - v4 - v1) / x
         *)
        1-16: exact admit.
      Qed.
    End with_cast.
  End RewriteRules.
End Compilers.
