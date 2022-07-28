Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.MiscCompilerPasses.
Require Import Crypto.MiscCompilerPassesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.API.Compilers.
  Import Language.Wf.Compilers.
  Import Language.WfExtra.Compilers.
  Import MiscCompilerPasses.Compilers.
  Import MiscCompilerPassesProofs.Compilers.
  Import expr.Notations.
  Import invert_expr.
  Import Compilers.API.

  Module Subst01.
    Import MiscCompilerPassesProofs.Compilers.Subst01.

    Definition Interp_Subst01 is_ident_always_live {t} e Hwf
      := @Interp_Subst01 _ ident is_ident_always_live _ (@ident.interp) (@ident.interp_Proper) t e Hwf.
  End Subst01.

#[global]
  Hint Resolve Subst01.Wf_Subst01 : wf_extra.
#[global]
  Hint Opaque Subst01.Subst01 : wf_extra interp_extra.
#[global]
  Hint Rewrite @Subst01.Interp_Subst01 : interp_extra.

  Module DeadCodeElimination.
    Import MiscCompilerPassesProofs.Compilers.DeadCodeElimination.

    Definition Interp_EliminateDead is_ident_always_live {t} e Hwf
      := @Interp_EliminateDead _ ident is_ident_always_live _ (@ident.interp) (@ident.interp_Proper) t e Hwf.
  End DeadCodeElimination.

#[global]
  Hint Resolve DeadCodeElimination.Wf_EliminateDead : wf_extra.
#[global]
  Hint Opaque DeadCodeElimination.EliminateDead : wf_extra interp_extra.
#[global]
  Hint Rewrite @DeadCodeElimination.Interp_EliminateDead : interp_extra.
End Compilers.
