Require Import Crypto.Util.Sigma.Lift.
Require Import Crypto.Util.Sigma.Associativity.
Require Import Crypto.Util.Sigma.MapProjections.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Eta.
Require Export Coq.ZArith.ZArith.
Require Export Crypto.Util.LetIn.
Require Export Crypto.Util.FixedWordSizes.
Require Export Crypto.Compilers.Syntax.
Require Export Crypto.Specific.IntegrationTestDisplayCommonTactics.
Require Export Crypto.Compilers.Z.HexNotationConstants.
Require Export Crypto.Util.Notations.
Require Export Crypto.Compilers.Z.CNotations.

Global Arguments Pos.to_nat !_ / .
Global Arguments InterpEta {_ _ _ _ _}.
Global Set Printing Width 2000000.

Notation "'Interp-η' f x" := (Eta.InterpEta f x) (format "'Interp-η' '//' f '//' x", at level 200, f at next level, x at next level).
Notation ReturnType := (interp_flat_type _).
Notation "'let' ( a , b ) := c 'in' d" := (let (a, b) := c in d) (at level 200, d at level 200, format "'let'  ( a ,  b )  :=  c  'in' '//' d").

Require Export Coq.Unicode.Utf8. (* for better line breaks at function display; must come last *)
