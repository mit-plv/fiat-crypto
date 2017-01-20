(** * Reserved Notations *)
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

(** Putting them all together in one file prevents conflicts.  Coq's
    parser (camlpX) is really bad at conflicting notation levels and
    is sometimes really bad at backtracking, too.  Not having level
    declarations in other files makes it harder for us to confuse
    Coq's parser. *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "()" (at level 0).
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
Reserved Infix ">>>" (at level 30, no associativity).
Reserved Infix "&'" (at level 50). (* N.B.  If we used '&', it would conflict with [{ a : T & P}] for [sigT] *)
Reserved Infix "∣" (at level 50).
Reserved Infix "~=" (at level 70).
Reserved Infix "==" (at level 70, no associativity).
Reserved Notation "x == y  :>  T"
         (at level 70, y at next level, no associativity).
Reserved Infix "=~>" (at level 70, no associativity).
Reserved Infix "<~=" (at level 70, no associativity).
Reserved Infix "<~=~>" (at level 70, no associativity).
Reserved Infix "≡" (at level 70, no associativity).
Reserved Infix "≢" (at level 70, no associativity).
Reserved Infix "≡_n" (at level 70, no associativity).
Reserved Infix "≢_n" (at level 70, no associativity).
Reserved Infix "≡_r" (at level 70, no associativity).
Reserved Infix "≢_r" (at level 70, no associativity).
Reserved Infix "≡ᵣ" (at level 70, no associativity).
Reserved Infix "≢ᵣ" (at level 70, no associativity).
Reserved Infix "≡₃₂" (at level 70, no associativity).
Reserved Infix "≢₃₂" (at level 70, no associativity).
Reserved Infix "≡₆₄" (at level 70, no associativity).
Reserved Infix "≢₆₄" (at level 70, no associativity).
Reserved Infix "≡₁₂₈" (at level 70, no associativity).
Reserved Infix "≢₁₂₈" (at level 70, no associativity).
Reserved Infix "≡₂₅₆" (at level 70, no associativity).
Reserved Infix "≢₂₅₆" (at level 70, no associativity).
Reserved Infix "≡₅₁₂" (at level 70, no associativity).
Reserved Infix "≢₅₁₂" (at level 70, no associativity).
Reserved Notation "a !== b" (at level 70, no associativity).
Reserved Notation "a ≢ b" (at level 70, no associativity).
Reserved Notation "$$ v" (at level 40).
Reserved Notation "& x" (at level 30).
Reserved Notation "** x" (at level 30).
Reserved Notation "A <- X ; B" (at level 70, right associativity).
Reserved Notation "u [ i ]" (at level 30).
Reserved Notation "v [[ i ]]" (at level 30).
Reserved Notation "u {{ i }}" (at level 30).
Reserved Notation "a # b" (at level 55, no associativity). (* match with theories/QArith/QArith_base.v *)
Reserved Notation "'plet' x := y 'in' z"
         (at level 200, z at level 200, format "'plet'  x  :=  y  'in' '//' z").
Reserved Notation "'slet' x := A 'in' b"
         (at level 200, b at level 200, format "'slet'  x  :=  A  'in' '//' b").
(* Note that making [Let] a keyword breaks the vernacular [Let] in Coq 8.4 *)
Reserved Notation "'dlet' x := y 'in' f"
         (at level 200, f at level 200, format "'dlet'  x  :=  y  'in' '//' f").
Reserved Notation "'pflet' x , pf := y 'in' f"
         (at level 200, f at level 200, format "'pflet'  x ,  pf  :=  y  'in' '//' f").
Reserved Notation "'λ'  x .. y , t" (at level 200, x binder, y binder, right associativity).
Reserved Notation "'λn'  x .. y , t" (at level 200, right associativity).
