Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.LanguageWf.
Require Import Crypto.UnderLetsProofs.
Require Import Crypto.GenerateIdentifiersWithoutTypes.
Require Import Crypto.GenerateIdentifiersWithoutTypesProofs.
Require Import Crypto.Rewriter.
Require Import Crypto.RewriterReify.
Require Import Crypto.RewriterWf1.
Require Import Crypto.RewriterWf1Tactics.
Require Import Crypto.RewriterWf2.
Require Import Crypto.RewriterInterpProofs1.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.ConstrFail.

Module Compilers.
  Import LanguageWf.Compilers.
  Import GenerateIdentifiersWithoutTypes.Compilers.
  Import GenerateIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.RewriteRules.
  Import RewriterReify.Compilers.RewriteRules.
  Import RewriterWf1.Compilers.RewriteRules.
  Import RewriterWf1Tactics.Compilers.RewriteRules.
  Import RewriterWf2.Compilers.RewriteRules.
  Import RewriterInterpProofs1.Compilers.RewriteRules.
  Import Rewriter.Compilers.RewriteRules.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.WfTactics.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.InterpTactics.GoalType.
  Import RewriterWf1Tactics.Compilers.RewriteRules.WfTactics.Tactic.
  Import RewriterWf1Tactics.Compilers.RewriteRules.InterpTactics.Tactic.

  Module Import RewriteRules.
    Import Compilers.pattern.ident.GoalType.
    Import Compilers.pattern.ProofGoalType.
    Definition VerifiedRewriter_of_Rewriter
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
              @Build_VerifiedRewriter (@Rewriter.Compilers.RewriteRules.GoalType.Rewrite pkg R) HWf HInterp_gen (HInterp_gen _));
        [ | clear HWf ]; intros.
      all: abstract (
               rewrite Rewrite_eq; cbv [Make.Rewrite]; rewrite rewrite_head_eq, all_rewrite_rules_eq, ?eq_invert_bind_args_unknown, ?eq_unify_unknown;
               first [ apply Compile.Wf_Rewrite; [ | assumption ];
                       let wf_do_again := fresh "wf_do_again" in
                       (intros ? ? ? ? wf_do_again ? ?);
                       eapply @Compile.wf_assemble_identifier_rewriters;
                       eauto using
                             pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct
                         with nocore;
                       try reflexivity
                     | eapply Compile.InterpRewrite; [ | assumption ];
                       intros; eapply Compile.interp_assemble_identifier_rewriters with (pident_to_typed:=@to_typed);
                       eauto using
                             pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct, pattern.ident.unify_to_typed,
                       @ident.gen_interp_Proper, eq_refl
                         with nocore ]).
    Defined.

    Ltac make_VerifiedRewriter pkg_proofs R RWf RInterp RProofs :=
      let res := (eval hnf in (@VerifiedRewriter_of_Rewriter _ pkg_proofs R RWf RInterp RProofs)) in
      let res := lazymatch res with
                 | context Res[@Build_VerifiedRewriter ?R]
                   => let t := fresh "t" in
                      let R' := fresh in
                      let R' := constr:(fun t
                                        => match R t return _ with
                                           | R' => ltac:(let v := (eval hnf in R') in exact v)
                                           end) in
                      context Res[@Build_VerifiedRewriter R']
                 end in
      res.

    Ltac Build_Rewriter pkg_proofs include_interp specs_proofs :=
      let pkg := lazymatch type of pkg_proofs with @package_proofs ?pkg => pkg end in
      let specs := lazymatch type of specs_proofs with
                   | PrimitiveHList.hlist (@snd bool Prop) ?specs => specs
                   | ?T
                     => let expected_type := uconstr:(PrimitiveHList.hlist (@snd bool Prop) ?[specs]) in
                        constr_fail_with ltac:(fun _ => fail 1 "Invalid type for specs_proofs:" T "Expected:" expected_type)
                   end in
      let R_name := fresh "Rewriter_data" in
      let R := Build_RewriterT pkg include_interp specs in
      let R := cache_term R R_name in
      let __ := Make.debug1 ltac:(fun _ => idtac "Proving Rewriter_Wf...") in
      let Rwf := fresh "Rewriter_Wf" in
      let Rwf := cache_proof_with_type_by (@Wf_GoalT pkg R) ltac:(idtac; prove_good ()) Rwf in
      let __ := Make.debug1 ltac:(fun _ => idtac "Proving Rewriter_Interp...") in
      let RInterp := fresh "Rewriter_Interp" in
      let RInterp := cache_proof_with_type_by (@Interp_GoalT pkg R) ltac:(idtac; prove_interp_good ()) RInterp in
      make_VerifiedRewriter pkg_proofs R Rwf RInterp specs_proofs.

    Module Export GoalType.
      Export RewriterWf1.Compilers.RewriteRules.GoalType.
    End GoalType.

    Module Export Tactic.
      Module Export Settings.
        Export RewriterReify.Compilers.RewriteRules.Tactic.Settings.
      End Settings.

      Ltac make_rewriter pkg_proofs include_interp specs_proofs :=
        let res := Build_Rewriter pkg_proofs include_interp specs_proofs in refine res.

      Tactic Notation "make_rewriter" constr(pkg_proofs) constr(include_interp) constr(specs_proofs) :=
        make_rewriter pkg_proofs include_interp specs_proofs.
    End Tactic.
  End RewriteRules.
End Compilers.
