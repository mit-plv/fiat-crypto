Require Import Crypto.RewriterAllTactics.
Require Import Crypto.Identifier.
Require Import Crypto.IdentifiersGENERATEDProofs.

Module Compilers.
  Import IdentifiersGENERATEDProofs.Compilers.pattern.ident.
  Import RewriterAllTactics.Compilers.
  Import Identifier.Compilers.

  Module RewriteRules.
    Module Export Tactic.
      Export RewriterAllTactics.Compilers.RewriteRules.Tactic.Settings.

      Ltac make_rewriter include_interp specs_proofs :=
        RewriterAllTactics.Compilers.RewriteRules.Tactic.make_rewriter ltac:(Identifier.Compilers.base.reify_base) ltac:(Identifier.Compilers.ident.reify) Identifier.Compilers.Classes.exprInfo Identifier.Compilers.Classes.exprExtraInfo IdentifiersGENERATEDProofs.Compilers.pattern.ident.package_proofs Identifier.Compilers.ident.is_var_like include_interp specs_proofs.

      Tactic Notation "make_rewriter" constr(include_interp) constr(specs_proofs) :=
        make_rewriter include_interp specs_proofs.
    End Tactic.
  End RewriteRules.
End Compilers.
