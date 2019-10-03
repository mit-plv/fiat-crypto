Require Import Coq.Classes.Morphisms.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.UnderLetsProofs.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Language.IdentifiersLibraryProofs.
Require Import Crypto.Rewriter.Rewriter.
Require Import Crypto.Rewriter.Reify.
Require Import Crypto.Rewriter.ProofsCommon.
Require Import Crypto.Rewriter.ProofsCommonTactics.
Require Import Crypto.Rewriter.Wf.
Require Import Crypto.Rewriter.InterpProofs.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.ConstrFail.

Module Compilers.
  Import Language.Wf.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.RewriteRules.
  Import Rewriter.Reify.Compilers.RewriteRules.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.
  Import Rewriter.ProofsCommonTactics.Compilers.RewriteRules.
  Import Rewriter.Wf.Compilers.RewriteRules.
  Import Rewriter.InterpProofs.Compilers.RewriteRules.
  Import Rewriter.Compilers.RewriteRules.GoalType.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.GoalType.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.WfTactics.GoalType.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.InterpTactics.GoalType.
  Import Rewriter.ProofsCommonTactics.Compilers.RewriteRules.WfTactics.Tactic.
  Import Rewriter.ProofsCommonTactics.Compilers.RewriteRules.InterpTactics.Tactic.

  Module Import RewriteRules.
    Import Compilers.pattern.ident.GoalType.
    Import Compilers.pattern.ProofGoalType.
    Import Compilers.Classes.

    Definition VerifiedRewriter_of_Rewriter
               {exprInfo : ExprInfoT}
               {exprExtraInfo : ExprExtraInfoT}
               {pkg : package}
               {pkg_proofs : package_proofs}
               (R : RewriterT)
               (RWf : Wf_GoalT R)
               (RInterp : Interp_GoalT R)
               (RProofs : PrimitiveHList.hlist
                            (@snd bool Prop)
                            (List.skipn (dummy_count (Rewriter_data R)) (rewrite_rules_specs (Rewriter_data R))))
    : VerifiedRewriter.
    Proof.
      simple refine
             (let HWf := _ in
              let HInterp_gen := _ in
              @Build_VerifiedRewriter exprInfo (@Rewriter.Compilers.RewriteRules.GoalType.Rewrite exprInfo exprExtraInfo pkg R) HWf HInterp_gen _ _ (@GeneralizeVar.Wf_via_flat _ ident _ _ _ _ _));
        [ | clear HWf ]; intros.
      all: abstract (
               rewrite Rewrite_eq; cbv [Make.Rewrite]; rewrite rewrite_head_eq, all_rewrite_rules_eq, ?eq_invert_bind_args_unknown, ?eq_unify_unknown;
               first [ apply (Compile.Wf_Rewrite _); [ | assumption ];
                       let wf_do_again := fresh "wf_do_again" in
                       (intros ? ? ? ? wf_do_again ? ?);
                       eapply @Compile.wf_assemble_identifier_rewriters;
                       eauto using
                             pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct,
                       eq_refl
                         with nocore typeclass_instances
                     | apply (Compile.InterpRewrite _); [ | assumption ];
                       intros; eapply Compile.interp_assemble_identifier_rewriters with (pident_to_typed:=@to_typed);
                       eauto using
                             (pattern.ident.unify_to_typed (pkg:=pkg)), pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct,
                       eq_refl
                         with nocore ]).
    Defined.

    Ltac make_VerifiedRewriter exprInfo exprExtraInfo pkg pkg_proofs R RWf RInterp RProofs :=
      let res := (eval hnf in (@VerifiedRewriter_of_Rewriter exprInfo exprExtraInfo pkg pkg_proofs R RWf RInterp RProofs)) in
      let res := lazymatch res with
                 | context Res[@Build_VerifiedRewriter ?exprInfo ?R]
                   => let t := fresh "t" in
                      let R' := fresh in
                      let R' := constr:(fun t
                                        => match R t return _ with
                                           | R' => ltac:(let v := (eval hnf in R') in exact v)
                                           end) in
                      context Res[@Build_VerifiedRewriter exprInfo R']
                 end in
      res.

    Ltac Build_Rewriter reify_base reify_ident exprInfo exprExtraInfo pkg_proofs ident_is_var_like include_interp specs_proofs :=
      let pkg := lazymatch type of pkg_proofs with @package_proofs ?base ?ident ?pkg => pkg end in
      let specs := lazymatch type of specs_proofs with
                   | PrimitiveHList.hlist (@snd bool Prop) ?specs => specs
                   | ?T
                     => let expected_type := uconstr:(PrimitiveHList.hlist (@snd bool Prop) ?[specs]) in
                        constr_fail_with ltac:(fun _ => fail 1 "Invalid type for specs_proofs:" T "Expected:" expected_type)
                   end in
      let R_name := fresh "Rewriter_data" in
      let R := Build_RewriterT reify_base reify_ident exprInfo exprExtraInfo pkg ident_is_var_like include_interp specs in
      let R := cache_term R R_name in
      let __ := Make.debug1 ltac:(fun _ => idtac "Proving Rewriter_Wf...") in
      let Rwf := fresh "Rewriter_Wf" in
      let Rwf := cache_proof_with_type_by (@Wf_GoalT exprInfo exprExtraInfo pkg R) ltac:(idtac; prove_good ()) Rwf in
      let __ := Make.debug1 ltac:(fun _ => idtac "Proving Rewriter_Interp...") in
      let RInterp := fresh "Rewriter_Interp" in
      let RInterp := cache_proof_with_type_by (@Interp_GoalT exprInfo exprExtraInfo pkg R) ltac:(idtac; prove_interp_good ()) RInterp in
      make_VerifiedRewriter exprInfo exprExtraInfo pkg pkg_proofs R Rwf RInterp specs_proofs.

    Module Import FinalTacticHelpers.
      Lemma generalize_to_eqv {base_type base_interp} {A B f g}
            (H : @type.related base_type base_interp (fun _ => eq) (type.arrow A B) f g)
        : forall x, Proper (@type.eqv A) x -> f x == g x.
      Proof. intro; apply H. Qed.

      Lemma eq_trans_eqv {base_type base_interp T x y z}
            (H1 : x = y)
            (H2 : @type.related base_type base_interp (fun _ => eq) T y z)
        : x == z.
      Proof. subst; assumption. Qed.

      Lemma eq_trans_eqv_Interp {base_type base_interp ident ident_interp T x y z}
            (H2 : @type.related base_type base_interp (fun _ => eq) T (@expr.Interp base_type ident base_interp ident_interp T y) z)
            (H1 : x = y)
        : (@expr.Interp base_type ident base_interp ident_interp T x) == z.
      Proof. subst; assumption. Qed.

      Ltac generalize_hyps_for_rewriting base reify_type base_interp :=
        let base_type := constr:(base.type base) in
        let base_type_interp := constr:(base.interp base_interp) in
        (*let reify_base_type T := base.reify base reify_base T in
        let reify_type T := type.reify reify_base_type (base.type base) T in*)
        intros;
        repeat match goal with
               | [ |- @eq ?T ?x ?y ] => let t := reify_type T in
                                        change (@type.related _ base_type_interp (fun _ => eq) t x y)
               | [ H := _ |- _ ] => revert H
               | [ H : ?T |- @type.related _ base_type_interp (fun _ => eq) ?B _ _ ]
                 => let t := reify_type T in
                    generalize (_ : Proper (@type.related _ base_type_interp (fun _ => eq) t) H);
                    revert H;
                    refine (@generalize_to_eqv _ base_type_interp t B _ _ _)
               | [ H : ?T |- _ ] => clear H
               end.

      Ltac etransitivity_for_sides do_lhs do_rhs :=
        intros;
        let LHS := match goal with |- ?LHS = ?RHS => LHS end in
        let RHS := match goal with |- ?LHS = ?RHS => RHS end in
        let LHS' := open_constr:(_) in
        let RHS' := open_constr:(_) in
        transitivity RHS';
        [ transitivity LHS'; [ symmetry | shelve ] | ];
        [ lazymatch do_lhs with true => idtac | false => reflexivity end
        | lazymatch do_rhs with true => idtac | false => reflexivity end ].

      Ltac do_reify_rhs ident ident_interp := notypeclasses refine (@expr.Reify_rhs _ ident _ ident_interp _ _ _ _ _ _); [ typeclasses eauto | ].
      Ltac do_rewrite_with verified_rewriter_package :=
        refine (eq_trans_eqv_Interp _ _);
        [ refine (@Interp_gen_Rewrite verified_rewriter_package _ _ _ _);
          [ .. | prove_Wf () ]
        | lazymatch goal with
          | [ |- ?ev = ?RHS ] => let RHS' := (eval vm_compute in RHS) in
                                 unify ev RHS'; vm_cast_no_check (eq_refl RHS)
          end ].

      Ltac do_final_cbv base_interp ident_gen_interp :=
        let base_interp_head := head base_interp in
        let ident_gen_interp_head := head ident_gen_interp in
        cbv [expr.Interp expr.interp Classes.ident_gen_interp Classes.ident_interp type.interp base.interp base_interp_head ident_gen_interp_head ident.literal ident.eagerly ident.cast2].

      Ltac Rewrite_for_gen verified_rewriter_package do_lhs do_rhs :=
        lazymatch (eval hnf in (exprInfo verified_rewriter_package)) with
        | {| base := ?base
             ; ident := ?ident
             ; base_interp := ?base_interp
             ; ident_gen_interp := ?ident_gen_interp
          |}
          => let base_type := constr:(base.type base) in
             let base_type_interp := constr:(base.interp base_interp) in
             let reify_type := type.reify_via_tc base_type base_type_interp in
             let ident_interp := constr:(@ident_gen_interp ident.cast_outside_of_range) in
             unshelve (
                 solve [
                     etransitivity_for_sides do_lhs do_rhs;
                     generalize_hyps_for_rewriting base reify_type base_interp;
                     do_reify_rhs ident ident_interp;
                     do_rewrite_with verified_rewriter_package
               ]);
             do_final_cbv base_interp ident_gen_interp
        end.
    End FinalTacticHelpers.

    Module Export GoalType.
      Export Rewriter.ProofsCommon.Compilers.RewriteRules.GoalType.
    End GoalType.

    Module Export Tactic.
      Module Export Settings.
        Export Rewriter.Reify.Compilers.RewriteRules.Tactic.Settings.
      End Settings.

      Ltac make_rewriter reify_base reify_ident exprInfo exprExtraInfo pkg_proofs ident_is_var_like include_interp specs_proofs :=
        let res := Build_Rewriter reify_base reify_ident exprInfo exprExtraInfo pkg_proofs ident_is_var_like include_interp specs_proofs in refine res.

      Tactic Notation "make_rewriter" tactic3(reify_base) tactic3(reify_ident) constr(exprInfo) constr(exprExtraInfo) constr(pkg_proofs) constr(ident_is_var_like) constr(include_interp) constr(specs_proofs) :=
        make_rewriter reify_base reify_ident exprInfo exprExtraInfo pkg_proofs ident_is_var_like include_interp specs_proofs.


      Ltac Rewrite_lhs_for verified_rewriter_package := Rewrite_for_gen verified_rewriter_package true false.
      Ltac Rewrite_rhs_for verified_rewriter_package := Rewrite_for_gen verified_rewriter_package false true.
      Ltac Rewrite_for verified_rewriter_package := Rewrite_for_gen verified_rewriter_package true true.
    End Tactic.
  End RewriteRules.
End Compilers.
