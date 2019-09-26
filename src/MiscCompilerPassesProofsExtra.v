Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.Identifier.
Require Import Crypto.IdentifierExtra.
Require Import Crypto.LanguageWf.
Require Import Crypto.LanguageWfExtra.
Require Import Crypto.MiscCompilerPasses.
Require Import Crypto.MiscCompilerPassesProofs.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import Identifier.Compilers.
  Import IdentifierExtra.Compilers.
  Import LanguageWf.Compilers.
  Import LanguageWfExtra.Compilers.
  Import MiscCompilerPasses.Compilers.
  Import MiscCompilerPassesProofs.Compilers.
  Import expr.Notations.
  Import invert_expr.
  Import Compilers.defaults.

  Module Subst01.
    Import MiscCompilerPassesProofs.Compilers.Subst01.

    Definition Interp_gen_Subst01 {cast_outside_of_range} {t} e Hwf
      := @Interp_Subst01 _ ident _ (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.
  End Subst01.

  Hint Resolve Subst01.Wf_Subst01 : wf_extra.
  Hint Rewrite @Subst01.Interp_gen_Subst01 : interp_extra.

  Module DeadCodeElimination.
    Import MiscCompilerPassesProofs.Compilers.DeadCodeElimination.

    Definition Interp_gen_EliminateDead {cast_outside_of_range} {t} e Hwf
      := @Interp_EliminateDead _ ident _ (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.
  End DeadCodeElimination.

  Hint Resolve DeadCodeElimination.Wf_EliminateDead : wf_extra.
  Hint Rewrite @DeadCodeElimination.Interp_gen_EliminateDead : interp_extra.
End Compilers.
