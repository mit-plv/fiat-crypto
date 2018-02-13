Require Import Crypto.Util.Strings.Equality.
Require Import Coq.Strings.Ascii.

Local Open Scope char_scope.

(** Special characters *)

Example Null := "000".
Example Backspace := "008".
Example Tab := "009".
Example LF := "010".
Example NewPage := "012".
Example CR := "013".
Example Escape := "027".
Example NewLine := "010".
