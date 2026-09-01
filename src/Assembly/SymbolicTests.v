From Coq Require Import String.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Symbolic.

Local Open Scope string_scope.

Example parse_p2align_as_unsupported_alignment :
  finalize parse_RawLine ".p2align 4, 0xc3" = Some (ALIGN "4, 0xc3").
Proof. reflexivity. Qed.

Lemma symex_alignment_is_unsupported
      {opts : symbolic_options_computed_opt} {descr : description} amount st :
  SymexRawLine (ALIGN amount) st
  = Error (error.unsupported_line (ALIGN amount), st).
Proof. reflexivity. Qed.

Lemma symex_ascii_is_unsupported
      {opts : symbolic_options_computed_opt} {descr : description} s st :
  SymexRawLine (ASCII s) st
  = Error (error.unsupported_line (ASCII s), st).
Proof. reflexivity. Qed.

Lemma symex_asciz_is_unsupported
      {opts : symbolic_options_computed_opt} {descr : description} s st :
  SymexRawLine (ASCIZ s) st
  = Error (error.unsupported_line (ASCIZ s), st).
Proof. reflexivity. Qed.
