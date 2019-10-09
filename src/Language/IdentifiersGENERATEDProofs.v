Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.PrimitiveSigma.
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.IdentifiersBasicGENERATED.
Require Import Crypto.Language.IdentifiersGENERATED.
Require Import Crypto.Language.IdentifiersGenerateProofs.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Export IdentifiersGenerateProofs.Compilers.
  Import IdentifiersGENERATED.Compilers.
  Module pattern.
    Export IdentifiersGenerateProofs.Compilers.pattern.
    Import IdentifiersGENERATED.Compilers.pattern.
    Module ident.
      Export IdentifiersGenerateProofs.Compilers.pattern.ident.
      Import IdentifiersGENERATED.Compilers.pattern.ident.

      Import ProofTactic.Settings.

      Definition package_proofs : @ProofGoalType.package_proofs_with_args Compilers.base Compilers.ident package IdentifiersBasicGENERATED.Compilers.package.
      Proof. ProofTactic.prove_package_proofs. Qed.
    End ident.
  End pattern.
End Compilers.
