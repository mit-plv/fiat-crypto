Require Import Crypto.Rewriter.AllTactics.
Require Import Crypto.Rewriter.ProofsCommon.
Require Import Crypto.Language.IdentifiersBasicGENERATED.
Require Import Crypto.Language.IdentifiersGENERATEDProofs.

Module Compilers.
  Import IdentifiersGENERATEDProofs.Compilers.pattern.ident.
  Import Rewriter.AllTactics.Compilers.

  Module RewriteRules.
    Module GoalType.
      Export ProofsCommon.Compilers.RewriteRules.GoalType.
      Notation VerifiedRewriter_with_args := (VerifiedRewriter_with_args IdentifiersBasicGENERATED.Compilers.package IdentifiersGENERATEDProofs.Compilers.pattern.ident.package_proofs) (only parsing).
    End GoalType.

    Module Export Tactic.
      Export Rewriter.AllTactics.Compilers.RewriteRules.Tactic.Settings.

      Ltac make_rewriter_via include_interp specs_proofs :=
        Rewriter.AllTactics.Compilers.RewriteRules.Tactic.make_rewriter_via IdentifiersBasicGENERATED.Compilers.package IdentifiersGENERATEDProofs.Compilers.pattern.ident.package_proofs include_interp specs_proofs.

      Tactic Notation "make_rewriter_via" constr(include_interp) constr(specs_proofs) :=
        make_rewriter_via include_interp specs_proofs.
    End Tactic.
  End RewriteRules.
End Compilers.
