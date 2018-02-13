Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.

Scheme Equality for ascii.
Scheme Equality for string.

Infix "=?" := ascii_beq : char_scope.
Infix "=?" := string_beq : string_scope.
