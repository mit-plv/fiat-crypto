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
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.ForallIn.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.
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

    Section good.
      Context {var1 var2 : type -> Type}.

      Local Notation rewrite_rules_goodT := (@Compile.rewrite_rules_goodT ident pattern.ident (@pattern.ident.arg_types) var1 var2).

      Lemma wf_list_rect {T A}
            G N1 N2 C1 C2 ls1 ls2
            (HN : Compile.wf_value G N1 N2)
            (HC : forall G' x1 x2 xs1 xs2 rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> Compile.wf_value G x1 x2
                -> List.Forall2 (Compile.wf_value G) xs1 xs2
                -> Compile.wf_value G' rec1 rec2
                -> Compile.wf_value G' (C1 x1 xs1 rec1) (C2 x2 xs2 rec2))
            (Hls : List.Forall2 (Compile.wf_value G) ls1 ls2)
        : Compile.wf_value
            G
            (list_rect (fun _ : list (@Compile.value base.type ident var1 (type.base T))
                        => @Compile.value base.type ident var1 A)
                       N1 C1 ls1)
            (list_rect (fun _ : list (@Compile.value base.type ident var2 (type.base T))
                        => @Compile.value base.type ident var2 A)
                       N2 C2 ls2).
      Proof. induction Hls; cbn [list_rect]; try eapply HC; eauto using (ex_intro _ nil). Qed.

      Lemma wf_nat_rect {A}
            G O1 O2 S1 S2 n
            (HO : Compile.wf_value_with_lets G O1 O2)
            (HS : forall G' n rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> Compile.wf_value_with_lets G' rec1 rec2
                -> Compile.wf_value_with_lets G' (S1 n rec1) (S2 n rec2))
        : Compile.wf_value_with_lets
            G
            (nat_rect (fun _ => @Compile.value_with_lets base.type ident var1 A) O1 S1 n)
            (nat_rect (fun _ => @Compile.value_with_lets base.type ident var2 A) O2 S2 n).
      Proof. induction n; cbn [nat_rect]; try eapply HS; eauto using (ex_intro _ nil). Qed.

      Global Strategy -100 [rewrite_rules Compile.rewrite_rules_goodT_curried_cps].

      Local Ltac start_good :=
        match goal with
        | [ |- rewrite_rules_goodT ?rew1 ?rew2 ]
          => let H := fresh in
             pose proof (@Compile.rewrite_rules_goodT_by_curried _ _ _ _ _ rew1 rew2 eq_refl) as H;
             let data := lazymatch rew1 with rewrite_rules ?data _ => data end in
             let h := head data in
             cbv [h rewrite_rules] in H;
             let h' := lazymatch type of H with
                       | context[Compile.rewrite_rules_goodT_curried_cps ?pident_arg_types ?rew1] => head rew1
                       end in
             let pident_arg_types
                 := lazymatch type of H with
                    | context[Compile.rewrite_rules_goodT_curried_cps ?pident_arg_types ?rew1] => pident_arg_types
                    end in
             cbv [h' pident_arg_types Compile.rewrite_rules_goodT_curried_cps] in H;
             (* make [Qed] not take forever by explicitly recording a cast node *)
             let H' := fresh in
             pose proof H as H'; clear H;
             apply H'; clear H'; intros
        end.

      Local Ltac fin_wf :=
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

      Local Ltac handle_reified_rewrite_rules :=
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

      Local Ltac handle_extra_nbe :=
        repeat first [ match goal with
                       | [ |- expr.wf _ (reify_list _) (reify_list _) ] => rewrite expr.wf_reify_list
                       | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
                       | [ |- List.Forall2 _ (List.map _ _) (List.map _ _) ] => rewrite Forall2_map_map_iff
                       | [ |- List.Forall _ (seq _ _) ] => rewrite Forall_seq
                       end
                     | progress intros
                     | progress fin_wf ].

      Local Notation nbe_rewrite_rules := (rewrite_rules nbe_rewriter_data _).
      Lemma nbe_rewrite_rules_good
        : rewrite_rules_goodT nbe_rewrite_rules nbe_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: abstract (handle_reified_rewrite_rules; handle_extra_nbe).
      Qed.

      Local Ltac handle_extra_arith_rules :=
        repeat first [ progress cbv [option_eq SubstVarLike.is_var_fst_snd_pair_opp_cast] in *
                     | break_innermost_match_step
                     | match goal with
                       | [ Hwf : Compile.wf_value _ ?x _, H : context[SubstVarLike.is_recursively_var_or_ident _ ?x] |- _ ] => erewrite SubstVarLike.wfT_is_recursively_var_or_ident in H by exact Hwf
                       end
                     | congruence
                     | progress fin_wf ].

      Local Notation arith_rewrite_rules max_const := (rewrite_rules (arith_rewriter_data max_const) _).
      Lemma arith_rewrite_rules_good max_const
        : rewrite_rules_goodT (arith_rewrite_rules max_const) (arith_rewrite_rules max_const).
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules; handle_extra_arith_rules.
      Time Qed.

      Local Notation arith_with_casts_rewrite_rules := (rewrite_rules arith_with_casts_rewriter_data _).
      Lemma arith_with_casts_rewrite_rules_good
        : rewrite_rules_goodT arith_with_casts_rewrite_rules arith_with_casts_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Time Qed.

      Local Notation strip_literal_casts_rewrite_rules := (rewrite_rules strip_literal_casts_rewriter_data _).
      Lemma strip_literal_casts_rewrite_rules_good
        : rewrite_rules_goodT strip_literal_casts_rewrite_rules strip_literal_casts_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Time Qed.

      Local Notation fancy_rewrite_rules invert_low invert_high := (rewrite_rules (fancy_rewriter_data invert_low invert_high) _).
      Lemma fancy_rewrite_rules_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_goodT (fancy_rewrite_rules invert_low invert_high) (fancy_rewrite_rules invert_low invert_high).
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Time Qed.

      Local Notation fancy_with_casts_rewrite_rules invert_low invert_high value_range flag_range := (rewrite_rules (fancy_with_casts_rewriter_data invert_low invert_high value_range flag_range) _).
      Lemma fancy_with_casts_rewrite_rules_good
            (invert_low invert_high : Z -> Z -> option Z)
            (value_range flag_range : ZRange.zrange)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_goodT (fancy_with_casts_rewrite_rules invert_low invert_high value_range flag_range) (fancy_with_casts_rewrite_rules invert_low invert_high value_range flag_range).
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Time Qed.
    End good.
  End RewriteRules.
End Compilers.
