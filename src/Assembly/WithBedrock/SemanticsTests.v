(** Regression tests for the treatment of non-instruction lines by the
    concrete semantics; these must agree with the symbolic executor
    (see src/Assembly/SymbolicTests.v and scrutineer finding #2512). *)
From Coq Require Import String.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.WithBedrock.Semantics.

Lemma DenoteRawLine_ASCII_ st nul s : DenoteRawLine st (ASCII_ nul s) = None.
Proof. reflexivity. Qed.

Lemma DenoteRawLine_DIRECTIVE st d
  : DenoteRawLine st (DIRECTIVE d) = if inert_directive d then Some st else None.
Proof. cbv [DenoteRawLine]; break_innermost_match; reflexivity. Qed.

Lemma DenoteRawLine_ALIGN st a : DenoteRawLine st (ALIGN a) = None.
Proof. reflexivity. Qed.
