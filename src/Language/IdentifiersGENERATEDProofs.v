Require Import Rewriter.Language.Language.
Require Import Crypto.Language.IdentifiersBasicGENERATED.
Require Import Crypto.Language.IdentifiersGENERATED.
Require Import Rewriter.Language.IdentifiersGenerateProofs.

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
