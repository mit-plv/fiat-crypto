From Coq Require Import String.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.WithBedrock.Semantics.

Lemma denote_ascii_is_unsupported st s :
  Semantics.DenoteRawLine st (ASCII s) = None.
Proof. reflexivity. Qed.

Lemma denote_asciz_is_unsupported st s :
  Semantics.DenoteRawLine st (ASCIZ s) = None.
Proof. reflexivity. Qed.
