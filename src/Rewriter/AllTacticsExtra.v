Require Import Crypto.Rewriter.AllTactics.
Require Import Crypto.Language.API.
Require Import Crypto.Language.IdentifiersGENERATEDProofs.

Module Compilers.
  Import IdentifiersGENERATEDProofs.Compilers.pattern.ident.
  Import Rewriter.AllTactics.Compilers.
  Import API.Compilers.

  Module RewriteRules.
    Module Export Tactic.
      Export Rewriter.AllTactics.Compilers.RewriteRules.Tactic.Settings.

      Ltac make_rewriter include_interp specs_proofs :=
        Rewriter.AllTactics.Compilers.RewriteRules.Tactic.make_rewriter ltac:(API.Compilers.base.reify_base) ltac:(API.Compilers.ident.reify) API.Compilers.Classes.exprInfo API.Compilers.Classes.exprExtraInfo IdentifiersGENERATEDProofs.Compilers.pattern.ident.package_proofs API.Compilers.ident.is_var_like include_interp specs_proofs.

      Tactic Notation "make_rewriter" constr(include_interp) constr(specs_proofs) :=
        make_rewriter include_interp specs_proofs.
    End Tactic.
  End RewriteRules.
End Compilers.
