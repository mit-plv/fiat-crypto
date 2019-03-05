Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.LanguageWf.
Require Import Crypto.UnderLetsProofs.
Require Import Crypto.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Rewriter.
Require Import Crypto.RewriterWf1.
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
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.OperationsBounds.
Require Import Crypto.Util.Tactics.NormalizeCommutativeIdentifier.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Forall.
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

      Local Lemma unfold_is_bounded_by_bool v r
        : is_bounded_by_bool v r = true -> lower r <= v <= upper r.
      Proof using Type.
        cbv [is_bounded_by_bool]; intro; split_andb; Z.ltb_to_lt; split; assumption.
      Qed.

      Local Lemma unfold_is_tighter_than_bool r1 r2
        : is_tighter_than_bool r1 r2 = true -> lower r2 <= lower r1 /\ upper r1 <= upper r2.
      Proof using Type.
        cbv [is_tighter_than_bool]; intro; split_andb; Z.ltb_to_lt; split; assumption.
      Qed.

      Local Notation rewrite_rules_interp_goodT := (@Compile.rewrite_rules_interp_goodT ident pattern.ident (@pattern.ident.arg_types) (@pattern.ident.to_typed) (@ident_interp)).

      Local Ltac do_cbv0 :=
        cbv [id
               Compile.rewrite_rules_interp_goodT_curried
               Compile.rewrite_rule_data_interp_goodT_curried Compile.under_with_unification_resultT_relation_hetero Compile.under_with_unification_resultT'_relation_hetero Compile.wf_with_unification_resultT Compile.under_type_of_list_relation_cps Compile.under_type_of_list_relation1_cps pattern.pattern_of_anypattern pattern.type_of_anypattern Compile.rew_replacement Compile.rew_should_do_again Compile.rew_with_opt Compile.rew_under_lets Compile.wf_with_unification_resultT Compile.pattern_default_interp pattern.type.under_forall_vars_relation pattern.type.under_forall_vars_relation1 Compile.deep_rewrite_ruleTP_gen Compile.with_unification_resultT' pattern.ident.arg_types pattern.type.lam_forall_vars Compilers.pattern.type.lam_forall_vars_gen Compile.pattern_default_interp' pattern.collect_vars PositiveMap.empty pattern.type.collect_vars PositiveSet.elements PositiveSet.union pattern.base.collect_vars PositiveSet.empty PositiveSet.xelements Compile.lam_type_of_list id pattern.ident.to_typed Compile.under_type_of_list_relation_cps Compile.deep_rewrite_ruleTP_gen_good_relation Compile.normalize_deep_rewrite_rule pattern.type.subst_default PositiveSet.add PositiveSet.rev PositiveSet.rev_append PositiveMap.add Compile.option_bind' Compile.wf_value Compile.value pattern.base.subst_default pattern.base.lookup_default PositiveMap.find Compile.rewrite_ruleTP ident.smart_Literal Compile.value_interp_related].
      Local Ltac do_cbv :=
        do_cbv0;
        cbv [List.map List.fold_right List.rev list_rect orb List.app].

      Local Ltac start_interp_good :=
        apply Compile.rewrite_rules_interp_goodT_by_curried;
        do_cbv;
        lazymatch goal with
        | [ |- forall x p, In (@existT ?A ?P x p) ?ls -> @?Q x p ]
          => let Q' := fresh in
             pose Q as Q';
             change (forall x p, In (@existT A P x p) ls -> Q' x p);
             apply (@forall_In_existT A P Q' ls); subst Q'; cbv [projT1 projT2 id]
        end;
        do_cbv0;
        repeat first [ progress intros
                     | match goal with
                       | [ |- { pf : ?x = ?x | _ } ] => (exists eq_refl)
                       | [ |- True /\ _ ] => split; [ exact I | ]
                       | [ |- _ /\ _ ] => split; [ intros; exact I | ]
                       end
                     | progress cbn [eq_rect] in * ];
        cbn [fst snd base.interp base.base_interp type.interp projT1 projT2 UnderLets.interp expr.interp type.related ident.gen_interp UnderLets.interp_related] in *.

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
             progress cbn [ident_interp fst snd]
        | [ |- ?x = ?y ] => tryif first [ has_evar x | has_evar y ] then fail else (progress subst)
        | [ |- ?x = ?x ] => tryif has_evar x then fail else reflexivity
        | [ |- ?ev = _ ] => is_evar ev; reflexivity
        | [ |- _ = ?ev ] => is_evar ev; reflexivity
        end.

      Local Ltac interp_good_t_step_related :=
        first [ lazymatch goal with
                | [ |- ?x = ?x ] => reflexivity
                | [ |- True ] => exact I
                | [ H : ?x = true, H' : ?x = false |- _ ] => exfalso; clear -H H'; congruence
                | [ |- ?G ] => has_evar G; reflexivity
                | [ |- context[expr.interp_related_gen _ _ _ _] ] => reflexivity
                | [ |- context[_ == _] ] => reflexivity
                (*| [ |- context[(fst ?x, snd ?x)] ] => progress eta_expand
                | [ |- context[match ?x with pair a b => _ end] ] => progress eta_expand*)
                end
              | progress cbn [expr.interp ident.gen_interp fst snd Compile.reify Compile.reflect Compile.wf_value' Compile.value' Option.bind UnderLets.interp list_case type.interp base.interp base.base_interp ident.to_fancy invert_Some ident.fancy.interp ident.fancy.interp_with_wordmax Compile.reify_expr bool_rect UnderLets.interp_related type.related] in *
              | progress cbv [Compile.option_bind' respectful expr.interp_related] in *
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
                | [ |- UnderLets.interp_related _ _ (list_rect _ _ _ _) (List.app ?ls1 ?ls2) ]
                  =>  rewrite (eq_app_list_rect ls1 ls2)
                | [ |- UnderLets.interp_related _ _ (list_rect _ _ _ _) (@flat_map ?A ?B ?f ?ls) ]
                  =>  rewrite (@eq_flat_map_list_rect A B f ls)
                | [ |- UnderLets.interp_related _ _ (list_rect _ _ _ _) (@partition ?A ?f ?ls) ]
                  =>  rewrite (@eq_partition_list_rect A f ls)
                | [ |- UnderLets.interp_related _ _ (list_rect _ _ _ _) (@List.map ?A ?B ?f ?ls) ]
                  => rewrite (@eq_map_list_rect A B f ls)
                | [ |- UnderLets.interp_related _ _ _ (@fold_right ?A ?B ?f ?v ?ls) ]
                  =>  rewrite (@eq_fold_right_list_rect A B f v ls)
                | [ |- context[expr.interp_related_gen _ _ (reify_list _)] ]
                  => rewrite expr.reify_list_interp_related_gen_iff
                | [ H : context[expr.interp_related_gen _ _ (reify_list _)] |- _ ]
                  => rewrite expr.reify_list_interp_related_gen_iff in H
                | [ |- context[Forall2 _ (List.map _ _) _] ] => rewrite Forall2_map_l_iff
                | [ |- context[Forall2 _ _ (List.map _ _)] ] => rewrite Forall2_map_r_iff
                | [ |- context[Forall2 _ (List.repeat _ _) (List.repeat _ _)] ] => rewrite Forall2_repeat_iff
                | [ |- context[Forall2 _ (List.rev _) (List.rev _)] ] => rewrite Forall2_rev_iff
                | [ |- context[Forall2 _ ?x ?x] ] => rewrite Forall2_Forall; cbv [Proper]
                | [ |- context[Forall _ (seq _ _)] ] => rewrite Forall_seq
                | [ H : Forall2 ?R ?l1 ?l2 |- Forall2 ?R (List.firstn ?n ?l1) (List.firstn ?n ?l2) ]
                  => apply Forall2_firstn, H
                | [ H : Forall2 ?R ?l1 ?l2 |- Forall2 ?R (List.skipn ?n ?l1) (List.skipn ?n ?l2) ]
                  => apply Forall2_skipn, H
                | [ |- Forall2 ?R (List.combine _ _) (List.combine _ _) ]
                  => eapply Forall2_combine; [ | eassumption | eassumption ]
                | [ H : List.Forall2 _ ?l1 ?l2, H' : ?R ?v1 ?v2 |- ?R (nth_default ?v1 ?l1 ?x) (nth_default ?v2 ?l2 ?x) ]
                  => apply Forall2_forall_iff''; split; assumption
                | [ H : List.Forall2 _ ?x ?y |- List.length ?x = List.length ?y ]
                  => eapply eq_length_Forall2, H
                | [ |- exists fv xv, _ /\ _ /\ fv xv = ?f ?x ]
                  => exists f, x; repeat apply conj; [ solve [ repeat interp_good_t_step_related ] | | reflexivity ]
                | [ |- _ /\ ?x = ?x ] => split; [ | reflexivity ]
                | [ |- UnderLets.interp_related
                         ?ident_interp ?R
                         (list_rect
                            (fun _ : list (expr ?A) => UnderLets.UnderLets _ _ _ ?B)
                            ?Pnil
                            ?Pcons
                            ?ls)
                         (list_rect
                            (fun _ : list _ => ?B')
                            ?Pnil'
                            ?Pcons'
                            ?ls') ]
                  => apply (@UnderLets.list_rect_interp_related _ _ _ ident_interp A B Pnil Pcons ls B' Pnil' Pcons' ls' R)
                | [ |- UnderLets.interp_related _ _ (nat_rect _ _ _ _) (nat_rect _ _ _ _) ]
                  => apply UnderLets.nat_rect_interp_related
                | [ |- UnderLets.interp_related _ _ (nat_rect _ _ _ _ _) (nat_rect _ _ _ _ _) ]
                  => eapply UnderLets.nat_rect_arrow_interp_related; [ .. | eassumption ]
                | [ |- UnderLets.interp_related _ _ (UnderLets.splice _ _) _ ]
                  => rewrite UnderLets.splice_interp_related_iff
                | [ |- UnderLets.interp_related ?ident_interp _ (UnderLets.splice_list _ _) _ ]
                  => apply UnderLets.splice_list_interp_related_of_ex with (RA:=expr.interp_related ident_interp); exists (fun x => x); eexists; repeat apply conj; [ | | reflexivity ]
                | [ H : UnderLets.interp_related _ _ ?e ?v1 |- UnderLets.interp_related _ _ ?e ?f ]
                  => let f := match (eval pattern v1 in f) with ?f _ => f end in
                     eapply (@UnderLets.interp_related_Proper_impl_same_UnderLets _ _ _ _ _ _ _ _ _ e v1 f); [ | exact H ]; cbv beta
                | [ H : forall x y, ?R x y -> UnderLets.interp_related _ _ (?e x) (?v1 y) |- UnderLets.interp_related _ _ (?e ?xv) ?f ]
                  => lazymatch f with
                     | context[v1 ?yv]
                       => let f := match (eval pattern (v1 yv) in f) with ?f _ => f end in
                          eapply (@UnderLets.interp_related_Proper_impl_same_UnderLets _ _ _ _ _ _ _ _ _ (e xv) (v1 yv) f); [ | eapply H; assumption ]
                     end
                | [ |- expr.interp_related_gen
                         _ _
                         (#(ident.prod_rect) @ ?f @ ?e)%expr
                         match ?e' with pair a b => @?f' a b end ]
                  => let fh := fresh in
                     let eh := fresh in
                     set (fh := f); set (eh := e); cbn [expr.interp_related_gen]; subst fh eh;
                     exists (fun ev => match ev with pair a b => f' a b end), e';
                     repeat apply conj;
                     [ | assumption | reflexivity ];
                     exists (fun fv ev => match ev with pair a b => fv a b end), f';
                     repeat apply conj;
                     [ cbn [type.interp type.related ident_interp]; cbv [respectful]; intros; subst; eta_expand; auto | | reflexivity ]
                | [ |- expr.interp_related_gen
                         _ _
                         (#(ident.bool_rect) @ ?t @ ?f @ ?b)%expr
                         (bool_rect ?P ?t' ?f' ?b') ]
                  => let th := fresh in
                     let fh := fresh in
                     let bh := fresh in
                     set (th := t); set (fh := f); set (bh := b); cbn [expr.interp_related_gen]; subst th fh bh;
                     unshelve
                       ((exists (bool_rect P t' f'), b'); repeat apply conj;
                        [ | shelve | reflexivity ];
                        (exists (fun fv => bool_rect P t' (fv tt)), (fun _ => f')); repeat apply conj;
                        [ | shelve | reflexivity ];
                        (exists (fun tv fv => bool_rect P (tv tt) (fv tt)), (fun _ => t')); repeat apply conj;
                        [ | shelve | reflexivity ])
                | [ |- @expr.interp_related_gen _ _ _ _ _ _ (type.base ?t) _ _ ]
                  => lazymatch t with
                     | base.type.type_base base.type.Z => idtac
                     | base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z) => idtac
                     end;
                     progress repeat recurse_interp_related_step
                | [ |- exists (fv : ?T1 -> ?T2) (ev : ?T1),
                      _ /\ _ /\ fv ev = ?x ]
                  => lazymatch T1 with Z => idtac | (Z * Z)%type => idtac end;
                     lazymatch T2 with Z => idtac | (Z * Z)%type => idtac end;
                     progress repeat recurse_interp_related_step
                | [ |- expr.interp_related_gen _ _ (expr.Abs ?f) _ ]
                  => let fh := fresh in set (fh := f); cbn [expr.interp_related_gen]; subst fh
                | [ H : expr.interp_related_gen _ _ ?x ?x' |- expr.interp_related_gen _ _ (?f @ ?x) (?f' ?x') ]
                  => let fh := fresh in
                     let xh := fresh in
                     set (fh := f); set (xh := x); cbn [expr.interp_related_gen]; subst fh xh;
                     exists f', x'; repeat apply conj;
                     [ | exact H | reflexivity ]
                | [ |- List.Forall2 _ (update_nth _ _ _) (update_nth _ _ _) ] => apply Forall2_update_nth
                | [ H : zrange * zrange |- _ ] => destruct H
                end
              | progress intros
              | progress subst
              | assumption
              | progress inversion_option
              | progress destruct_head'_and
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
                  => apply f_equal3; [ reflexivity | reflexivity | solve [ repeat interp_good_t_step_related ] ]
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
              | progress destruct_head'_or
              | progress cbn [expr.interp_related_gen] in *
              | match goal with
                | [ H : context[expr.interp _ (UnderLets.interp _ (?f _ _ _))]
                    |- expr.interp _ (UnderLets.interp _ (?f _ _ _)) = _ ]
                  => apply H
                | [ H : forall x1 x2, ?R1 x1 x2 -> ?R2 (?f1 x1) (?f2 x2) |- ?R2 (?f1 _) (?f2 _) ]
                  => apply H
                | [ H : forall x1 x2, ?R1 x1 x2 -> forall y1 y2, ?R2 y1 y2 -> ?R3 (?f1 x1 y1) (?f2 x2 y2) |- ?R3 (?f1 _ _) (?f2 _ _) ]
                  => apply H
                | [ H : forall x x', ?Rx x x' -> forall y y', _ -> forall z z', ?Rz z z' -> ?R (?f x y z) (?f' x' y' z') |- ?R (?f _ _ _) (?f' _ _ _) ]
                  => apply H; clear H
                end
              | progress cbv [Option.bind] in *
              | match goal with
                | [ H : expr.interp_related_gen _ _ ?e ?v |- _ ] => is_var e; clear H e
                end ].

      Local Ltac interp_good_t_step_arith :=
        first [ lazymatch goal with
                | [ |- ?x = ?x ] => reflexivity
                | [ |- True ] => exact I
                | [ H : ?x = true, H' : ?x = false |- _ ] => exfalso; clear -H H'; congruence
                end
              | match goal with
                | [ H : context[ZRange.normalize (ZRange.normalize _)] |- _ ]
                  => rewrite ZRange.normalize_idempotent in H
                | [ |- context[ZRange.normalize (ZRange.normalize _)] ]
                  => rewrite ZRange.normalize_idempotent
                | [ |- context[ident.cast (ZRange.normalize ?r)] ]
                  => rewrite ident.cast_normalize
                | [ H : context[ident.cast (ZRange.normalize ?r)] |- _ ]
                  => rewrite ident.cast_normalize in H
                | [ H : ?T, H' : ?T |- _ ] => clear H'
                | [ H : context[is_bounded_by_bool _ (ZRange.normalize (-_))] |- _ ]
                  => rewrite ZRange.is_bounded_by_bool_move_opp_normalize in H
                | [ |- context[is_bounded_by_bool _ (ZRange.normalize (-_))] ]
                  => rewrite ZRange.is_bounded_by_bool_move_opp_normalize
                | [ H : is_bounded_by_bool ?v (ZRange.normalize ?r) = true |- context[ident.cast _ ?r ?v] ]
                  => rewrite (@ident.cast_in_normalized_bounds _ r v) by exact H
                | [ H : is_bounded_by_bool ?v (ZRange.normalize ?r) = true |- context[ident.cast _ (-?r) (-?v)] ]
                  => rewrite (@ident.cast_in_normalized_bounds _ (-r) (-v));
                     [ | clear -H ]
                | [ |- context[ident.cast _ ?r (-ident.cast _ (-?r) ?v)] ]
                  => rewrite (ident.cast_in_normalized_bounds r (-ident.cast _ (-r) v))
                    by (rewrite <- ZRange.is_bounded_by_bool_move_opp_normalize; apply ident.cast_always_bounded)
                | [ |- context[ident.cast _ ?r (ident.cast _ ?r _)] ]
                  => rewrite (@ident.cast_idempotent _ _ r)
                | [ H : is_bounded_by_bool _ ?r = true |- _]
                  => is_var r; unique pose proof (ZRange.is_bounded_by_normalize _ _ H)
                | [ H : lower ?x = upper ?x |- _ ] => is_var x; destruct x; cbn [upper lower] in *
                | [ H : is_bounded_by_bool ?x (ZRange.normalize r[?y~>?y]) = true |- _ ]
                  => apply ZRange.is_bounded_by_bool_normalize_constant_iff in H
                | [ H : is_bounded_by_bool ?x r[?y~>?y] = true |- _ ]
                  => apply ZRange.is_bounded_by_bool_constant_iff in H
                end
              | progress intros
              | progress subst
              | assumption
              | progress destruct_head'_and
              | progress Z.ltb_to_lt
              | progress split_andb
              | match goal with
                | [ |- ?a mod ?b = ?a' mod ?b ] => apply f_equal2; lia
                | [ |- ?a / ?b = ?a' / ?b ] => apply f_equal2; lia
                | [ |- Z.opp _ = Z.opp _ ] => apply f_equal
                end
              | break_innermost_match_step
              | break_innermost_match_hyps_step
              | progress destruct_head'_or
              | match goal with
                | [ |- context[-ident.cast _ (-?r) (-?v)] ] => rewrite (ident.cast_opp' r v)
                | [ |- context[ident.cast ?coor ?r ?v] ]
                  => is_var v;
                     pose proof (@ident.cast_always_bounded coor r v);
                     generalize dependent (ident.cast coor r v); clear v; intro v; intros
                | [ |- context[ident.cast ?coor ?r ?v] ]
                  => is_var v; is_var coor;
                     pose proof (@ident.cast_cases coor r v);
                     generalize dependent (ident.cast coor r v); intros
                | [ H : is_bounded_by_bool ?v ?r = true, H' : is_tighter_than_bool ?r ?r' = true |- _ ]
                  => unique assert (is_bounded_by_bool v r' = true) by (eauto 2 using ZRange.is_bounded_by_of_is_tighter_than)
                | [ H : is_bounded_by_bool (-?v) ?r = true, H' : (-?r <=? ?r')%zrange = true |- _ ]
                  => unique assert (is_bounded_by_bool v r' = true)
                    by (apply (@ZRange.is_bounded_by_of_is_tighter_than _ _ H');
                        rewrite <- ZRange.is_bounded_by_bool_opp, ZRange.opp_involutive; exact H)
                | [ H : is_bounded_by_bool ?v (-?r) = true |- _ ]
                  => is_var v;
                     unique assert (is_bounded_by_bool (-v) r = true)
                       by now rewrite <- ZRange.is_bounded_by_bool_move_opp_normalize, ZRange.normalize_opp
                | [ H : is_bounded_by_bool ?x r[0~>?v-1] = true |- _ ]
                  => progress (try unique assert (0 <= x); try unique assert (x <= v - 1));
                     [ clear -H; cbv [is_bounded_by_bool] in H; cbn [lower upper] in H; Bool.split_andb; Z.ltb_to_lt; lia..
                     | ]
                end
              | progress cbn [expr.interp_related_gen] in *
              | match goal with
                | [ |- context[Z.shiftl] ] => rewrite Z.shiftl_mul_pow2 by auto with zarith
                | [ |- context[Z.shiftr] ] => rewrite Z.shiftr_div_pow2 by auto with zarith
                | [ |- context[Z.shiftl _ (-_)] ] => rewrite Z.shiftl_opp_r
                | [ |- context[Z.land _ (Z.ones _)] ] => rewrite Z.land_ones by auto using Z.log2_nonneg
                | [ |- context[- - _] ] => rewrite Z.opp_involutive
                | [ H : ?x = 2^Z.log2 ?x |- context[2^Z.log2 ?x] ] => rewrite <- H
                | [ H : ?x = 2^?n |- context[Z.land _ (?x - 1)] ]
                  => rewrite !Z.sub_1_r, H, <- Z.ones_equiv, Z.land_ones by auto with zarith
                | [ |- _ = _ :> BinInt.Z ] => progress normalize_commutative_identifier Z.land Z.land_comm
                | [ H : ?x = ?y, H' : ?x <> ?y |- _ ] => exfalso; apply H', H
                | [ H : ?x = 2^Z.log2_up ?x - 1 |- context[2^Z.log2_up ?x - 1] ] => rewrite <- H
                | [ H : ?x = 2^Z.log2 ?x, H' : context[2^Z.log2 ?x] |- _ = _ :> BinInt.Z ]
                  => rewrite <- H in H'
                | [ |- _ = _ :> BinInt.Z ] => progress autorewrite with zsimplify_const
                | [ H : 0 <= ?x, H' : ?x <= ?r - 1 |- context[?x mod ?r] ]
                  => rewrite (Z.mod_small x r) by (clear -H H'; lia)
                | [ H : 0 <= ?x, H' : ?x <= ?y - 1 |- context[?x / ?y] ]
                  => rewrite (Z.div_small x y) by (clear -H H'; lia)
                | [ H : ?x = 2^Z.log2 ?x |- _ ]
                  => unique assert (0 <= x) by (rewrite H; auto with zarith)
                | [ |- _ mod ?x = _ mod ?x ]
                  => progress (push_Zmod; pull_Zmod)
                | [ |- ?f (_ mod ?x) = ?f (_ mod ?x) ]
                  => progress (push_Zmod; pull_Zmod)
                | [ |- _ mod ?x = _ mod ?x ]
                  => apply f_equal2; (lia + nia)
                | _ => rewrite !Z.shiftl_mul_pow2 in * by auto using Z.log2_nonneg
                | _ => rewrite !Z.land_ones in * by auto using Z.log2_nonneg
                | H : ?x mod ?b * ?y <= _
                  |- context [ (?x * ?y) mod ?b ] =>
                  rewrite (PullPush.Z.mul_mod_l x y b);
                  rewrite (Z.mod_small (x mod b * y) b) by omega
                | [ |- context[_ - ?x + ?x] ] => rewrite !Z.sub_add
                | [ |- context[_ mod (2^_) * 2^_] ] => rewrite <- !Z.mul_mod_distr_r_full
                | [ |- context[Z.land _ (Z.ones _)] ] => rewrite !Z.land_ones by lia
                | [ |- context[2^?a * 2^?b] ] => rewrite <- !Z.pow_add_r by lia
                | [ |- context[-?x + ?y] ] => rewrite !Z.add_opp_l
                | [ |- context[?n + - ?m] ] => rewrite !Z.add_opp_r
                | [ |- context[?n - - ?m] ] => rewrite !Z.sub_opp_r
                | [ |- context[Zpos ?p * ?x / Zpos ?p] ]
                  => rewrite (@Z.div_mul' x (Zpos p)) in * by (clear; lia)
                | [ H : context[Zpos ?p * ?x / Zpos ?p] |- _ ]
                  => rewrite (@Z.div_mul' x (Zpos p)) in * by (clear; lia)
                | [ |- ?f (?a mod ?r) = ?f (?b mod ?r) ] => apply f_equal; apply f_equal2; lia
                | [ |- context[-?a - ?b + ?c] ] => replace (-a - b + c) with (c - a - b) by (clear; lia)
                | [ |- context[?x - ?y + ?z] ]
                  => lazymatch goal with
                     | [ |- context[z - y + x] ]
                       => progress replace (z - y + x) with (x - y + z) by (clear; lia)
                     end
                | [ |- context[?x - ?y - ?z] ]
                  => lazymatch goal with
                     | [ |- context[x - z - y] ]
                       => progress replace (x - z - y) with (x - y - z) by (clear; lia)
                     end
                | [ |- context[?x + ?y] ]
                  => lazymatch goal with
                     | [ |- context[y + x] ]
                       => progress replace (y + x) with (x + y) by (clear; lia)
                     end
                | [ |- context[?x + ?y + ?z] ]
                  => lazymatch goal with
                     | [ |- context[x + z + y] ]
                       => progress replace (x + z + y) with (x + y + z) by (clear; lia)
                     | [ |- context[z + x + y] ]
                       => progress replace (z + x + y) with (x + y + z) by (clear; lia)
                     | [ |- context[z + y + x] ]
                       => progress replace (z + y + x) with (x + y + z) by (clear; lia)
                     | [ |- context[y + x + z] ]
                       => progress replace (y + x + z) with (x + y + z) by (clear; lia)
                     | [ |- context[y + z + x] ]
                       => progress replace (y + z + x) with (x + y + z) by (clear; lia)
                     end
                | [ |- - ident.cast _ (-?r) (- (?x / ?y)) = ident.cast _ ?r (?x' / ?y) ]
                  => tryif constr_eq x x' then fail else replace x with x' by lia
                | [ |- _ = _ :> BinInt.Z ] => progress autorewrite with zsimplify_fast
                end ].

      Local Ltac remove_casts :=
        repeat match goal with
               | [ |- context[ident.cast _ ?r (ident.cast _ ?r _)] ]
                 => rewrite ident.cast_idempotent
               | [ H : context[ident.cast _ ?r (ident.cast _ ?r _)] |- _ ]
                 => rewrite ident.cast_idempotent in H
               | [ |- context[ident.cast ?coor ?r ?v] ]
                 => is_var v;
                    pose proof (@ident.cast_always_bounded coor r v);
                    generalize dependent (ident.cast coor r v);
                    clear v; intro v; intros
               | [ H : context[ident.cast ?coor ?r ?v] |- _ ]
                 => is_var v;
                    pose proof (@ident.cast_always_bounded coor r v);
                    generalize dependent (ident.cast coor r v);
                    clear v; intro v; intros
               | [ H : context[ZRange.constant ?v] |- _ ] => unique pose proof (ZRange.is_bounded_by_bool_normalize_constant v)
               | [ H : is_tighter_than_bool (?ZRf ?r1 ?r2) (ZRange.normalize ?rs) = true,
                       H1 : is_bounded_by_bool ?v1 ?r1 = true,
                            H2 : is_bounded_by_bool ?v2 ?r2 = true
                   |- _ ]
                 => let cst := multimatch goal with
                               | [ |- context[ident.cast ?coor rs (?Zf v1 v2)] ] => constr:(ident.cast coor rs (Zf v1 v2))
                               | [ H : context[ident.cast ?coor rs (?Zf v1 v2)] |- _ ] => constr:(ident.cast coor rs (Zf v1 v2))
                               end in
                    lazymatch cst with
                    | ident.cast ?coor rs (?Zf v1 v2)
                      => let lem := lazymatch constr:((ZRf, Zf)%core) with
                                    | (ZRange.shiftl, Z.shiftl)%core => constr:(@ZRange.is_bounded_by_bool_shiftl v1 r1 v2 r2 H1 H2)
                                    | (ZRange.shiftr, Z.shiftr)%core => constr:(@ZRange.is_bounded_by_bool_shiftr v1 r1 v2 r2 H1 H2)
                                    | (ZRange.land, Z.land)%core => constr:(@ZRange.is_bounded_by_bool_land v1 r1 v2 r2 H1 H2)
                                    end in
                         try unique pose proof (@ZRange.is_bounded_by_of_is_tighter_than _ _ H _ lem);
                         clear H;
                         rewrite (@ident.cast_in_normalized_bounds coor rs (Zf v1 v2)) in * by assumption
                    end
               | [ H : is_tighter_than_bool (?ZRf ?r1) (ZRange.normalize ?rs) = true,
                       H1 : is_bounded_by_bool ?v1 ?r1 = true
                   |- _ ]
                 => let cst := multimatch goal with
                               | [ |- context[ident.cast ?coor rs (?Zf v1)] ] => constr:(ident.cast coor rs (Zf v1))
                               | [ H : context[ident.cast ?coor rs (?Zf v1)] |- _ ] => constr:(ident.cast coor rs (Zf v1))
                               end in
                    lazymatch cst with
                    | ident.cast ?coor rs (?Zf v1)
                      => let lem := lazymatch constr:((ZRf, Zf)%core) with
                                    | (ZRange.cc_m ?s, Z.cc_m ?s)%core => constr:(@ZRange.is_bounded_by_bool_cc_m s v1 r1 H1)
                                    end in
                         try unique pose proof (@ZRange.is_bounded_by_of_is_tighter_than _ _ H _ lem);
                         clear H;
                         rewrite (@ident.cast_in_normalized_bounds coor rs (Zf v1)) in * by assumption
                    end
               | [ H : is_bounded_by_bool ?v (ZRange.normalize ?r) = true |- context[ident.cast ?coor ?r ?v] ]
                 => rewrite (@ident.cast_in_normalized_bounds coor r v) in * by assumption
               | [ H : is_bounded_by_bool ?v (ZRange.normalize ?r) = true, H' : context[ident.cast ?coor ?r ?v] |- _ ]
                 => rewrite (@ident.cast_in_normalized_bounds coor r v) in * by assumption
               | [ H : is_bounded_by_bool ?v ?r = true,
                       H' : is_tighter_than_bool ?r r[0~>?x-1]%zrange = true,
                            H'' : Z.eqb ?x ?m = true
                   |- context[?v mod ?m] ]
                 => unique assert (is_bounded_by_bool v r[0~>x-1] = true)
                   by (eapply ZRange.is_bounded_by_of_is_tighter_than; eassumption)
               end.

      Local Ltac unfold_cast_lemmas :=
        repeat match goal with
               | [ H : context[ZRange.normalize (ZRange.constant _)] |- _ ]
                 => rewrite ZRange.normalize_constant in H
               | [ H : is_bounded_by_bool _ (ZRange.normalize ?r) = true |- _ ]
                 => is_var r; generalize dependent (ZRange.normalize r); clear r; intro r; intros
               | [ H : is_bounded_by_bool ?x (ZRange.constant ?x) = true |- _ ]
                 => clear H
               | [ H : is_bounded_by_bool ?x ?r = true |- _ ]
                 => is_var r; apply unfold_is_bounded_by_bool in H
               | [ H : is_bounded_by_bool ?x r[_~>_] = true |- _ ]
                 => apply unfold_is_bounded_by_bool in H
               | [ H : is_tighter_than_bool r[_~>_] r[_~>_] = true |- _ ]
                 => apply unfold_is_tighter_than_bool in H
               | _ => progress cbn [lower upper] in *
               | [ H : context[lower ?r] |- _ ]
                 => is_var r; let l := fresh "l" in let u := fresh "u" in destruct r as [l u]
               | [ H : context[upper ?r] |- _ ]
                 => is_var r; let l := fresh "l" in let u := fresh "u" in destruct r as [l u]
               | _ => progress Z.ltb_to_lt
               end.

      Local Ltac systematically_handle_casts :=
        remove_casts; unfold_cast_lemmas.

      Local Ltac fin_with_nia :=
        lazymatch goal with
        | [ |- ident.cast _ ?r _ = ident.cast _ ?r _ ] => apply f_equal; Z.div_mod_to_quot_rem; nia
        | _ => reflexivity || (Z.div_mod_to_quot_rem; (lia + nia))
        end.

      Lemma nbe_rewrite_rules_interp_good
        : rewrite_rules_interp_goodT nbe_rewrite_rules.
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [ repeat interp_good_t_step_related ].
      Qed.

      Lemma arith_rewrite_rules_interp_good max_const
        : rewrite_rules_interp_goodT (arith_rewrite_rules max_const).
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [ repeat interp_good_t_step_related; repeat interp_good_t_step_arith; fin_with_nia ].
      Qed.

      Lemma arith_with_casts_rewrite_rules_interp_good
        : rewrite_rules_interp_goodT arith_with_casts_rewrite_rules.
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [ repeat interp_good_t_step_related; repeat interp_good_t_step_arith; fin_with_nia ].
      Qed.

      Lemma strip_literal_casts_rewrite_rules_interp_good
        : rewrite_rules_interp_goodT strip_literal_casts_rewrite_rules.
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [ repeat interp_good_t_step_related; repeat interp_good_t_step_arith ].
      Qed.

      Local Ltac fancy_local_t :=
        repeat match goal with
               | [ H : forall s v v', ?invert_low s v = Some v' -> v = _,
                     H' : ?invert_low _ _ = Some _ |- _ ] => apply H in H'
               | [ H : forall s v v', ?invert_low s v = Some v' -> v = _ |- _ ]
                 => clear invert_low H
               end.
      Local Ltac more_fancy_arith_t := repeat autorewrite with zsimplify in *.

      Lemma fancy_rewrite_rules_interp_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_interp_goodT fancy_rewrite_rules.
      Proof using Type.
        Time start_interp_good.
        Time all: try solve [ repeat interp_good_t_step_related ].
      Qed.

      Lemma fancy_with_casts_rewrite_rules_interp_good
            (invert_low invert_high : Z -> Z -> option Z)
            (value_range flag_range : zrange)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_interp_goodT (fancy_with_casts_rewrite_rules invert_low invert_high value_range flag_range).
      Proof using Type.
        Time start_interp_good. (* Finished transaction in 1.206 secs (1.207u,0.s) (successful) *)
        Set Ltac Profiling.
        Reset Ltac Profile.
        Time all: repeat interp_good_t_step_related. (* Finished transaction in 13.259 secs (13.128u,0.132s) (successful) *)
        Reset Ltac Profile.
        Time all: fancy_local_t. (* Finished transaction in 0.051 secs (0.052u,0.s) (successful) *)
        Time all: systematically_handle_casts. (* Finished transaction in 2.004 secs (1.952u,0.052s) (successful) *)
        Time all: try solve [ repeat interp_good_t_step_arith ]. (* Finished transaction in 44.411 secs (44.004u,0.411s) (successful) *)
      Qed.
    End with_cast.
  End RewriteRules.
End Compilers.
