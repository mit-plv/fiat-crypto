(** * Reserved Notations *)
Require Export Crypto.Util.FixCoqMistakes.

(** Putting them all together in one file prevents conflicts.  Coq's
    parser (camlpX) is really bad at conflicting notation levels and
    is sometimes really bad at backtracking, too.  Not having level
    declarations in other files makes it harder for us to confuse
    Coq's parser. *)

Reserved Infix "=?" (at level 70, no associativity).
Reserved Infix "!=?" (at level 70, no associativity).
Reserved Infix "?=" (at level 70, no associativity).
Reserved Infix "?<" (at level 70, no associativity).
Reserved Infix ".+" (at level 50).
Reserved Infix ".*" (at level 50).
Reserved Notation "x ^ 2" (at level 30, format "x ^ 2").
Reserved Notation "x ^ 3" (at level 30, format "x ^ 3").
Reserved Infix "mod" (at level 40, no associativity).
Reserved Notation "'canonical' 'encoding' 'of' T 'as' B" (at level 50).
Reserved Infix "<<" (at level 30, no associativity).
Reserved Infix ">>" (at level 30, no associativity).
Reserved Infix "&" (at level 50).
Reserved Infix "∣" (at level 50).
Reserved Infix "~=" (at level 70).
