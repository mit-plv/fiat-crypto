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
Reserved Infix "∘" (at level 40, left associativity).
Reserved Infix "∘ᶠ" (at level 40, left associativity).
Reserved Infix "∘f" (at level 40, left associativity).
Reserved Infix "'o'" (at level 40, left associativity).
Reserved Infix "==" (at level 70, no associativity).
Reserved Infix "===" (at level 70, no associativity).
Reserved Infix "~=" (at level 70, no associativity).
Reserved Infix "=?" (at level 70, no associativity).
Reserved Infix "<?" (at level 70, no associativity).
Reserved Infix "<=?" (at level 70, no associativity).
Reserved Infix "!=?" (at level 70, no associativity).
Reserved Infix "?=" (at level 70, no associativity).
Reserved Infix "?<" (at level 70, no associativity).
Reserved Infix "=n?" (at level 70, no associativity).
Reserved Infix "=Z?" (at level 70, no associativity).
Reserved Infix "=ₙ?" (at level 70, no associativity).
Reserved Infix "=ℤ?" (at level 70, no associativity).
Reserved Infix "=ᶻ?" (at level 70, no associativity).
Reserved Infix "=ⁿ?" (at level 70, no associativity).
Reserved Infix ".+" (at level 50).
Reserved Infix ".*" (at level 50).
Reserved Notation "' x" (at level 20, no associativity, format "' x").
Reserved Notation "x ^ 2" (at level 30, format "x ^ 2").
Reserved Notation "x ^ 3" (at level 30, format "x ^ 3").
Reserved Notation "2 ^ e" (at level 30, format "2 ^ e", only printing).
Reserved Infix "mod" (at level 40, no associativity).
Reserved Notation "'canonical' 'encoding' 'of' T 'as' B" (at level 50).
Reserved Notation "@ 'is_eq_dec' T R" (at level 10, T at level 8, R at level 8).
Reserved Infix "@" (left associativity, at level 11).
Reserved Infix "@1" (left associativity, at level 11).
Reserved Infix "@₁" (left associativity, at level 11).
Reserved Infix "@@" (left associativity, at level 11).
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
Reserved Infix "≡_p" (at level 70, no associativity).
Reserved Infix "≢_p" (at level 70, no associativity).
Reserved Infix "≡ₚ" (at level 70, no associativity).
Reserved Infix "≢ₚ" (at level 70, no associativity).
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
(* Put these at level 71 so they don't conflict with the infix notations at level 70 *)
Reserved Notation "<" (at level 71).
Reserved Notation ">" (at level 71).
Reserved Notation "<=" (at level 71).
Reserved Notation ">=" (at level 71).
Reserved Notation "≤" (at level 71).
Reserved Notation "≥" (at level 71).
Reserved Notation "a !== b" (at level 70, no associativity).
Reserved Notation "a ≢ b" (at level 70, no associativity).
Reserved Notation "$$ v" (at level 40).
Reserved Notation "& x" (at level 30).
Reserved Notation "** x" (at level 30).
Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").
Reserved Notation "A <-- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <--  X ; '/' B ']'").
Reserved Notation "A <--- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <---  X ; '/' B ']'").
Reserved Notation "A <---- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <----  X ; '/' B ']'").
Reserved Notation "A <----- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-----  X ; '/' B ']'").
Reserved Notation "A ;; B" (at level 70, right associativity, format "'[v' A ;; '/' B ']'").
Reserved Notation "A ;;; B" (at level 70, right associativity, format "'[v' A ;;; '/' B ']'").
Reserved Notation "u [ i ]" (at level 30).
Reserved Notation "v [[ i ]]" (at level 30).
Reserved Notation "u {{ i }}" (at level 30).
Reserved Notation "a # b" (at level 55, no associativity). (* match with theories/QArith/QArith_base.v *)
Reserved Notation "'plet' x := y 'in' z"
         (at level 200, z at level 200, format "'plet'  x  :=  y  'in' '//' z").
Reserved Notation "'nlet' x := A 'in' b"
         (at level 200, b at level 200, x at level 99, format "'nlet'  x  :=  A  'in' '//' b").
Reserved Notation "'nlet' x : tx := A 'in' b"
         (at level 200, b at level 200, x at level 99, format "'nlet'  x  :  tx  :=  A  'in' '//' b").
Reserved Notation "'slet' x .. y := A 'in' b"
         (at level 200, x binder, y binder, b at level 200, format "'slet'  x .. y  :=  A  'in' '//' b").
Reserved Notation "'llet' x := A 'in' b"
         (at level 200, b at level 200, format "'llet'  x  :=  A  'in' '//' b").
Reserved Notation "'expr_let' x := A 'in' b"
         (at level 200, b at level 200, format "'expr_let'  x  :=  A  'in' '//' b").
Reserved Notation "'mlet' x := A 'in' b"
         (at level 200, b at level 200, format "'mlet'  x  :=  A  'in' '//' b").
(* Note that making [Let] a keyword breaks the vernacular [Let] in Coq 8.4 *)
Reserved Notation "'dlet_nd' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet_nd'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'pflet' x , pf := y 'in' f"
         (at level 200, f at level 200, format "'pflet'  x ,  pf  :=  y  'in' '//' f").
Reserved Notation "'λ' x .. y , t" (at level 200, x binder, y binder, right associativity, format "'λ'  x .. y , '//' t").
Reserved Notation "'λn'  x .. y , t" (at level 200, right associativity).
Reserved Notation "x ::> ( max_bitwidth = v )"
         (at level 70, no associativity, format "x  ::>  ( max_bitwidth  =  v )").
Reserved Notation "r[ l ~> u ]" (l at level 69, format "r[ l  ~>  u ]").
Reserved Notation "b[ l ~> u ]" (l at level 69, format "b[ l  ~>  u ]").
Reserved Notation "m[ l ~> u ]" (l at level 69, format "m[ l  ~>  u ]").
Reserved Notation "kv[ l ~> u ]" (l at level 69, format "kv[ l  ~>  u ]").
Reserved Notation "t[ l ~> u ]" (l at level 69, format "t[ l  ~>  u ]").
Reserved Notation "l[ l' ~> u ]" (l' at level 69, format "l[ l'  ~>  u ]").
Reserved Notation "'for' i (:= i0 ; += step ; < finish ) 'updating' ( state := initial ) {{ body }}"
         (at level 70, format "'[v  ' 'for'  i  (:=  i0 ;  +=  step ;  <  finish )  'updating'  ( state  :=  initial )  {{ '//' body ']' '//' }}").
Reserved Notation "'for' ( 'int' i = i0 ; step_expr ; finish_expr ) 'updating' ( state1 .. staten = initial ) {{ body }}"
         (at level 70, i at level 10, state1 binder, staten binder, format "'[v  ' 'for'  ( 'int'  i  =  i0 ;  step_expr ;  finish_expr )  'updating'  ( state1 .. staten  =  initial )  {{ '//' body ']' '//' }}").
Reserved Notation "x += y" (at level 70, no associativity).
Reserved Notation "x -= y" (at level 70, no associativity).
Reserved Notation "x ++" (at level 60, format "x ++").
Reserved Notation "x --" (at level 60, format "x --").
Reserved Notation "++ x" (at level 60, format "++ x").
Reserved Notation "-- x" (at level 60, format "-- x").
Reserved Notation "~> R" (at level 70).
Reserved Notation "A ~> R" (at level 99).
Reserved Notation "A --->" (left associativity, at level 65).
Reserved Notation "'return' x" (at level 70, format "'return'  x").
Reserved Notation "f x" (only printing, at level 10, left associativity).
(* TODO: Remove this next one if and when we drop support for Coq 8.7; it's present in the stdlib in 8.8 *)
Reserved Notation "{ x  &  P }" (at level 0, x at level 99).
(* TODO: Uncomment this block when https://github.com/mit-plv/bbv/pull/13 is merged
Reserved Notation "$ x" (at level 9, x at level 9, format "$ x").
Reserved Notation "# x" (at level 55, x at level 9, format "# x"). (* 55, so we don't clash with [_ # _] *)
 *)
Reserved Notation "## x" (at level 9, x at level 9, format "## x").
Reserved Notation "### x" (at level 9, x at level 9, format "### x").
Reserved Notation "\ x .. y , t" (at level 200, x binder, y binder, right associativity, format "\  x .. y , '//' t").

(* TODO: Remove these when https://github.com/mit-plv/bbv/pull/13 is merged *)
Reserved Notation "# x" (at level 0, format "# x").
