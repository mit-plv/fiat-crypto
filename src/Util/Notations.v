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
Reserved Notation "@ 'is_eq_dec' T R" (at level 10, T at level 8, R at level 8).
Reserved Infix "<<" (at level 30, no associativity).
Reserved Infix ">>" (at level 30, no associativity).
Reserved Infix "&" (at level 50).
Reserved Infix "∣" (at level 50).
Reserved Infix "~=" (at level 70).
Reserved Infix "==" (at level 70, no associativity).
Reserved Infix "≡" (at level 70, no associativity).
Reserved Infix "≢" (at level 70, no associativity).
Reserved Infix "≡_n" (at level 70, no associativity).
Reserved Infix "≢_n" (at level 70, no associativity).
Reserved Infix "≡_r" (at level 70, no associativity).
Reserved Infix "≢_r" (at level 70, no associativity).
Reserved Infix "≡ᵣ" (at level 70, no associativity).
Reserved Infix "≢ᵣ" (at level 70, no associativity).
Reserved Notation "a !== b" (at level 70, no associativity).
Reserved Notation "a ≢ b" (at level 70, no associativity).
Reserved Notation "$$ v" (at level 40).
Reserved Notation "% A" (at level 20, right associativity).
Reserved Notation "$ A" (at level 20, right associativity).
Reserved Notation "A :[ B ]:" (at level 20, right associativity).
Reserved Notation "# A" (at level 20, right associativity).
Reserved Notation "A :+: B" (at level 60, right associativity).
Reserved Notation "A :+c: B" (at level 60, right associativity).
Reserved Notation "A :-: B" (at level 60, right associativity).
Reserved Notation "A :&: B" (at level 45, right associativity).
Reserved Notation "A :^: B" (at level 45, right associativity).
Reserved Notation "A :>>: B" (at level 60, right associativity).
Reserved Notation "A :<<: B" (at level 60, right associativity).
Reserved Notation "A :*: B" (at level 55, right associativity).
(*Reserved Notation "O :( A , B ): :?: L ::: R" (at level 70, right associativity).*) (* breaks everything *)
Reserved Notation "F :**: e" (at level 70, right associativity).
Reserved Notation "E :->: F" (at level 70, right associativity).
Reserved Notation "A :|: B" (at level 65, left associativity).
Reserved Notation "n ::: A :():" (at level 65, left associativity).
Reserved Notation "& x" (at level 30).
Reserved Notation "** x" (at level 30).
Reserved Notation "A <- X ; B" (at level 70, right associativity).
Reserved Notation "'plet' x := y 'in' z" (at level 60).
Reserved Notation "u [ i ]" (at level 30).
Reserved Notation "v [[ i ]]" (at level 30).
Reserved Notation "u {{ i }}" (at level 30).
