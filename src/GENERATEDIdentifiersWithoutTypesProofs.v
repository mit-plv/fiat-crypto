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
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.GENERATEDIdentifiersWithoutTypes.
Require Import Crypto.GenerateIdentifiersWithoutTypesProofs.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Export GenerateIdentifiersWithoutTypesProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypes.Compilers.
  Module pattern.
    Export GenerateIdentifiersWithoutTypesProofs.Compilers.pattern.
    Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.
    Module ident.
      Export GenerateIdentifiersWithoutTypesProofs.Compilers.pattern.ident.
      Import GENERATEDIdentifiersWithoutTypes.Compilers.pattern.ident.

      Import ProofTactic.Settings.

      Definition package_proofs : @ProofGoalType.package_proofs package.
      Proof. ProofTactic.prove_package_proofs (). Qed.
    End ident.
  End pattern.
End Compilers.
