Require Import Crypto.Language.IdentifiersBasicGENERATED.
Require Import Crypto.Language.IdentifiersGenerate.

Module Compilers.
  Import IdentifiersBasicGENERATED.Compilers.
  Export IdentifiersGenerate.Compilers.

  Module pattern.
    Export IdentifiersGenerate.Compilers.pattern.
    Module ident.
      Export IdentifiersGenerate.Compilers.pattern.ident.

      Definition package : @GoalType.package Compilers.base Compilers.ident.
      Proof. Time Tactic.make_package IdentifiersBasicGENERATED.Compilers.package IdentifiersBasicGENERATED.Compilers.raw_ident IdentifiersBasicGENERATED.Compilers.pattern_ident. Defined.
    End ident.
  End pattern.
End Compilers.
