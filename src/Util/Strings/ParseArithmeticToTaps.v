Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Coq.QArith.QArith_base.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Notations.
Import ListNotations.
Local Open Scope option_scope.
Local Open Scope list_scope.
Local Open Scope char_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Open Scope parse_scope.

(** From the Python:
<<
# given a string representing one term or "tap" in a prime, returns a pair of
# integers representing the weight and coefficient of that tap
#    "2 ^ y" -> [1, y]
#    "x * 2 ^ y" -> [x, y]
#    "x * y" -> [x*y,0]
#    "x" -> [x,0]
def parse_term(t) :
    if "*" not in t and "^" not in t:
        return [int(t),0]

    if "*" in t:
        if len(t.split("*")) > 2: # this occurs when e.g. [w - x * y] has been turned into [w + -1 * x * y]
            a1,a2,b = t.split("*")
            a = int(a1) * int(a2)
        else:
            a,b = t.split("*")
        if "^" not in b:
            return [int(a) * int(b),0]
    else:
        a,b = (1,t)

    b,e = b.split("^")
    if int(b) != 2:
        raise NonBase2Exception("Could not parse term, power with base other than 2: %s" %t)
    return [int(a),int(e)]
>> *)

(** given an expression representing one term or "tap" in a prime,
    returns a pair of integers representing the coefficient and weight
    of that tap:
    * "2 ^ y" -> Some (2^y, 1)
    * "x * 2 ^ y" -> Some (2^y, x)
    * "x * y" -> Some (1,x*y)
    * "x" -> Some (1,x)
    *)
Fixpoint parse_term_of_Qexpr (v : Qexpr) : option (Z * Z)
  := match v with
     | Qvar x => match x with end
     | Qv x => q <- Q_to_Z_strict x; Some (1, q)
     | Qeopp a => v <- parse_term_of_Qexpr a; Some (fst v, -snd v)
     | Qeadd a b => None
     | Qesub a b => None
     | Qemul a b => b <- parse_term_of_Qexpr b;
                      a <- eval_Qexpr_strict a;
                      a <- Q_to_Z_strict a;
                      Some (fst b, a * snd b)
     | Qediv a b => None
     | Qepow b e => v <- eval_Qexpr_strict v; v <- Q_to_Z_strict v; Some (v, 1)
     end%option.

Fixpoint Qexpr_to_add_list (v : Qexpr) : list Qexpr
  := match v with
     | Qeadd a b => Qexpr_to_add_list a ++ Qexpr_to_add_list b
     | Qesub a b => Qexpr_to_add_list a ++ [Qeopp b]
     | v => [v]
     end.

(** Given a Qexpr which is a sequence of additions and subtractions,
    we return the value of the first component, and a list of the taps
    for the negation of the other components *)
Definition parse_prime_and_taps_of_Qexpr (v : Qexpr) : option (Z * list (Z * Z))
  := match Qexpr_to_add_list v with
     | nil => None
     | cons p taps
       => taps <- Option.List.lift (List.map (fun v => parse_term_of_Qexpr (Qeopp v)) taps);
            p <- eval_Qexpr_strict p;
            p <- Q_to_Z_strict p;
            Some (p, taps)
     end.

Definition parseZ_arith_to_taps (s : string) : option (Z * list (Z * Z))
  := v <- parseQexpr_arith s; parse_prime_and_taps_of_Qexpr v.

Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Example parse_v25519 : parse_prime_and_taps_of_Qexpr (2^255 - 19) = Some (2^255, [(1,19)]) := eq_refl.
Local Example parse_25519 : parseZ_arith_to_taps "2^255 - 19" = Some (2^255, [(1,19)]) := eq_refl.
Local Example parse_p521 : parseZ_arith_to_taps "2^521 - 1" = Some (2^521, [(1,1)]) := eq_refl.
Local Example parse_p448 : parseZ_arith_to_taps "2^448 - 2^224 - 1" = Some (2^448, [(2^224,1); (1,1)]) := eq_refl.
Local Example parse_p256 : parseZ_arith_to_taps "2^256 - 2^224 + 2^192 + 2^96 - 1" = Some (2^256, [(2^224,1); (2^192,-1); (2^96,-1); (1,1)]) := eq_refl.
Local Example parse_p434 : parseZ_arith_to_taps "2^216 * 3^137 - 1" = Some (2^216 * 3^137, [(1,1)]) := eq_refl.
