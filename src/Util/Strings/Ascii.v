From Coq Require Import NArith.
From Coq Require Import Ascii.
Require Import Crypto.Util.Notations.

Local Open Scope bool_scope.
Local Open Scope N_scope.
Local Open Scope char_scope.

(** Special characters *)

Example Null := "000".
Example Backspace := "008".
Example Tab := "009".
Example HorizontalTab := "009".
Example LF := "010".
Example NewLine := "010".
Example VerticalTab := "011".
Example NewPage := "012".
Example FormFeed := "012".
Example CR := "013".
Example Escape := "027".

Local Coercion N_of_ascii : ascii >-> N.
Definition ltb (x y : ascii) : bool := N.ltb x y.
Definition leb (x y : ascii) : bool := N.leb x y.
Infix "<?" := ltb : char_scope.
Infix "<=?" := leb : char_scope.

Definition is_upper (ch : ascii) : bool
  := ("A" <=? ch) && (ch <=? "Z").
Definition is_lower (ch : ascii) : bool
  := ("a" <=? ch) && (ch <=? "z").

Definition to_lower (ch : ascii) : ascii
  := if ("A" <=? ch) && (ch <=? "Z")
     then ascii_of_N ("a" + ch - "A")
     else ch.
Definition to_upper (ch : ascii) : ascii
  := if ("a" <=? ch) && (ch <=? "z")
     then ascii_of_N ("A" + ch - "a")
     else ch.

Definition is_whitespace (x : ascii) : bool
  := ((x =? " ") || (x =? NewPage) || (x =? LF) || (x =? CR) || (x =? Tab))%char%bool.

Definition is_printable (x : ascii) : bool
  := (" " <=? x) && (x <=? "~").
