Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.DefaultsProperties.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.InterpretToPHOASInterp.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.CompileInterp.
Require Import Crypto.Compilers.Named.WfFromUnit.
Require Import Crypto.Compilers.Named.DeadCodeEliminationInterp.
Require Import Crypto.Compilers.Named.WfInterp.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.RewriteAddToAdc.
Require Import Crypto.Compilers.Z.Named.RewriteAddToAdcInterp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.

Section language.
  Local Notation PContext var := (PositiveContext _ var _ internal_base_type_dec_bl).

  Lemma InterpRewriteAdc
        {t} (e : Expr base_type op t) (Hwf : Wf e)
  : forall x, Interp interp_op (RewriteAdc e) x = Interp interp_op e x.
  Proof.
    intro x; unfold RewriteAdc, option_map; break_innermost_match; try reflexivity;
      match goal with |- ?x = ?y => cut (Some x = Some y); [ congruence | ] end;
      (etransitivity; [ symmetry; eapply @Interp_InterpToPHOAS with (t:=Arrow _ _) | ]);
      repeat
        repeat
        first [ lazymatch goal with
                | [ H : DeadCodeElimination.EliminateDeadCode _ _ = Some ?e |- Syntax.Named.Interp ?e _ = Some _ ]
                  => let lhs := match goal with |- ?lhs = _ => lhs end in
                     let v := fresh in
                     (destruct lhs as [v|] eqn:?);
                     [ apply f_equal; eapply @InterpEliminateDeadCode with (Name_beq:=BinPos.Pos.eqb);
                       [ .. | eassumption | try eassumption | try eassumption ]; clear H | ]
                | [ |- Syntax.Named.Interp (RewriteAddToAdc.rewrite_expr _ ?e) _ = Some _ ]
                  => let lhs := match goal with |- ?lhs = _ => lhs end in
                     let H := fresh in
                     destruct lhs eqn:H; [ apply (f_equal (@Some _)); eapply @Interp_rewrite_expr in H | ]
                | [ H : Compile.compile (?e _) _ = Some ?e'', H' : Syntax.Named.Interp ?e'' ?x = Some ?v' |- ?v' = Interp ?interp_op' ?e ?x ]
                  => eapply @Interp_compile with (v:=x) (interp_op:=interp_op') in H
                end
              | intros; exact (@PositiveContextOk _ _ base_type_beq internal_base_type_dec_bl internal_base_type_dec_lb)
              | progress split_andb
              | congruence
              | tauto
              | solve [ auto | eapply @BinPos.Pos.eqb_eq; auto ]
              | eapply @Wf_from_unit
              | eapply @dec_rel_of_bool_dec_rel
              | eapply @internal_base_type_dec_lb
              | eapply @internal_base_type_dec_bl
              | eapply @InterpEliminateDeadCode; [ .. | eassumption | eassumption | ]
              | apply name_list_unique_DefaultNamesFor
              | progress intros
              | rewrite !@lookupb_empty
              | eapply @wf_from_unit with (uContext:=PContext _); [ .. | eassumption ]
              | match goal with
                | [ H : Syntax.Named.Interp ?e ?x = Some ?a, H' : Syntax.Named.Interp ?e ?x = Some ?b |- _ ]
                  => assert (a = b) by congruence; (subst a || subst b)
                end
              | lazymatch goal with
                | [ |- Some _ = Some _ ] => fail
                | [ |- None = Some _ ] => exfalso; eapply @wf_interp_not_None; [ .. | unfold Syntax.Named.Interp in *; eassumption ]
                | [ |- ?x = Some _ ] => destruct x eqn:?; [ apply f_equal | ]
                end ].
  Qed.
End language.

Hint Rewrite @InterpRewriteAdc using solve_wf_side_condition : reflective_interp.
