From Coq Require Import String List NArith.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Equivalence.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

Definition test_line (l : RawLine) : Line :=
  {| indent := ""
   ; rawline := l
   ; pre_comment_whitespace := ""
   ; comment := None
   ; line_number := 1 |}.

Definition test_ret : Line :=
  test_line (INSTR {| prefix := None; op := ret; args := [] |}).

Example strip_ret_rejects_ascii_after_ret s :
  strip_ret [test_ret; test_line (ASCII s)]
  = Error (Code_after_ret [test_line (ASCII s)] [test_line (ASCII s)]).
Proof. reflexivity. Qed.

Example strip_ret_rejects_asciz_after_ret s :
  strip_ret [test_ret; test_line (ASCIZ s)]
  = Error (Code_after_ret [test_line (ASCIZ s)] [test_line (ASCIZ s)]).
Proof. reflexivity. Qed.

Example strip_ret_rejects_p2align_after_ret :
  strip_ret [test_ret; test_line (ALIGN "4, 0xc3")]
  = Error (Code_after_ret [test_line (ALIGN "4, 0xc3")]
                          [test_line (ALIGN "4, 0xc3")]).
Proof. reflexivity. Qed.
