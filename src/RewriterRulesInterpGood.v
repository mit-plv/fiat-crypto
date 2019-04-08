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
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.ForallIn.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Option.
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
      Local Notation rewrite_rules_interp_goodT := (@Compile.rewrite_rules_interp_goodT ident pattern.ident (@pattern.ident.arg_types) (@pattern.ident.to_typed) (@ident_interp)).

      (** Coq >= 8.9 is much better at [eapply] than Coq <= Coq 8.8 *)
      Local Ltac cbv_type_for_Coq88 T :=
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
      Local Ltac cbv_for_Coq88_in H :=
        cbv [ident.Thunked.bool_rect ident.Thunked.list_case ident.Thunked.list_rect ident.Thunked.nat_rect ident.Thunked.option_rect];
        let T := type of H in
        let T := cbv_type_for_Coq88 T in
        change T in H.

      Local Ltac start_interp_good :=
        cbv [List.skipn] in *;
        lazymatch goal with
        | [ |- @Compile.rewrite_rules_interp_goodT ?ident ?pident ?pident_arg_types ?pident_to_typed ?ident_interp (rewrite_rules ?data ?var) ]
          => let H := fresh in
             pose proof (@Compile.rewrite_rules_interp_goodT_by_curried
                           _ _ _ pident_to_typed ident_interp (rewrite_rules data var) (rewrite_rules_specs data)) as H;
             let h := head data in
             cbv [rewrite_rules dummy_count rewrite_rules_specs h] in * |- ;
             let h' := lazymatch type of H with context[Compile.rewrite_rules_interp_goodT_curried_cps _ _ _ ?v] => head v end in
             unfold h' in H at 1;
             cbv [Compile.rewrite_rules_interp_goodT_curried_cps pident_arg_types pident_to_typed] in H;
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
             progress cbn [ident_interp fst snd]
        | [ |- ?x = ?y ] => tryif first [ has_evar x | has_evar y ] then fail else (progress subst)
        | [ |- ?x = ?y ] => tryif first [ has_evar x | has_evar y ] then fail else reflexivity
        | [ |- ?x = ?x ] => tryif has_evar x then fail else reflexivity
        | [ |- ?ev = _ ] => is_evar ev; reflexivity
        | [ |- _ = ?ev ] => is_evar ev; reflexivity
        end.

      (* TODO: MOVE ME? *)
      Local Ltac recursive_match_to_case term :=
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
      Local Ltac recursive_match_to_case_in_goal :=
        let G := match goal with |- ?G => G end in
        let G := recursive_match_to_case G in
        change G.

      Local Ltac preprocess_step :=
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
      Local Ltac preprocess := repeat preprocess_step.
      Local Ltac handle_extra_nbe :=
        repeat match goal with
               | [ |- UnderLets.interp_related _ _ (UnderLets.Base (expr.Ident _)) _ ]
                 => cbn [UnderLets.interp_related UnderLets.interp_related_gen expr.interp_related_gen ident_interp type.related]; reflexivity
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
                 => cbn [expr.interp_related_gen ident_interp type.related]; reflexivity
               end.
      Local Ltac fin_tac :=
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
      Local Ltac handle_reified_rewrite_rules_interp :=
        repeat first [ assumption
                     | match goal with
                       | [ |- UnderLets.interp_related _ _ (Reify.expr_value_to_rewrite_rule_replacement _ ?sda _) _ ]
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
                         => cbn [expr.interp_related_gen ident_interp type.related]; fin_tac
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
                       end ].


      Local Notation specT rewriter_data
        := (PrimitiveHList.hlist (@snd bool Prop) (List.skipn (dummy_count rewriter_data) (rewrite_rules_specs rewriter_data)))
             (only parsing).

      Lemma nbe_rewrite_rules_interp_good (H : specT nbe_rewriter_data)
        : rewrite_rules_interp_goodT (rewrite_rules nbe_rewriter_data _).
      Proof using Type.
        Time start_interp_good.
        Time all: preprocess; handle_extra_nbe; handle_reified_rewrite_rules_interp.
      Time Qed.

      Lemma arith_rewrite_rules_interp_good max_const (H : specT (arith_rewriter_data max_const))
        : rewrite_rules_interp_goodT (rewrite_rules (arith_rewriter_data max_const) _).
      Proof using Type.
        Time start_interp_good.
        Time all: preprocess; handle_reified_rewrite_rules_interp.
      Time Qed.

      Lemma arith_with_casts_rewrite_rules_interp_good (H : specT arith_with_casts_rewriter_data)
        : rewrite_rules_interp_goodT (rewrite_rules arith_with_casts_rewriter_data _).
      Proof using Type.
        Time start_interp_good.
        Time all: preprocess; handle_reified_rewrite_rules_interp.
      Time Qed.

      Lemma strip_literal_casts_rewrite_rules_interp_good (H : specT strip_literal_casts_rewriter_data)
        : rewrite_rules_interp_goodT (rewrite_rules strip_literal_casts_rewriter_data _).
      Proof using Type.
        Time start_interp_good.
        Time all: preprocess; handle_reified_rewrite_rules_interp.
      Time Qed.

      Lemma fancy_rewrite_rules_interp_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
            (H : specT (fancy_rewriter_data invert_low invert_high))
        : rewrite_rules_interp_goodT (rewrite_rules (fancy_rewriter_data invert_low invert_high) _).
      Proof using Type.
        Time start_interp_good.
        Time all: preprocess; handle_reified_rewrite_rules_interp.
      Time Qed.

      Lemma fancy_with_casts_rewrite_rules_interp_good
            (invert_low invert_high : Z -> Z -> option Z)
            (value_range flag_range : zrange)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
            (H : specT (fancy_with_casts_rewriter_data invert_low invert_high value_range flag_range))
        : rewrite_rules_interp_goodT (rewrite_rules (fancy_with_casts_rewriter_data invert_low invert_high value_range flag_range) _).
      Proof using Type.
        Time start_interp_good.
        Time all: preprocess; handle_reified_rewrite_rules_interp.
      Time Qed.
    End with_cast.
  End RewriteRules.
End Compilers.
