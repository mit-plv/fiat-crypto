Require Import Coq.NArith.NArith.
Require Import Crypto.Util.Strings.Equality.
Require Import Coq.Strings.Ascii.
Require Import Crypto.Util.Notations.

Local Open Scope bool_scope.
Local Open Scope N_scope.
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

Local Coercion N_of_ascii : ascii >-> N.
Definition ltb (x y : ascii) : bool := N.ltb x y.
Definition leb (x y : ascii) : bool := N.leb x y.
Infix "<?" := ltb : char_scope.
Infix "<=?" := leb : char_scope.

Definition to_lower (ch : ascii) : ascii
  := if ("A" <=? ch) && (ch <=? "Z")
     then ascii_of_N ("a" + ch - "A")
     else ch.
Definition to_upper (ch : ascii) : ascii
  := if ("a" <=? ch) && (ch <=? "z")
     then ascii_of_N ("A" + ch - "a")
     else ch.
