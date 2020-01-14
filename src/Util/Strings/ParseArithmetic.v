Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Equality.
Require Crypto.Util.Strings.Decimal.
Require Crypto.Util.Strings.OctalString.
Require Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Notations.
Import ListNotations.
Import BinPosDef.
Local Open Scope option_scope.
Local Open Scope list_scope.
Local Open Scope char_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope nat_scope.

Definition is_num (ch : ascii) : bool
  := (ascii_beq ch "0"
      || ascii_beq ch "1"
      || ascii_beq ch "2"
      || ascii_beq ch "3"
      || ascii_beq ch "4"
      || ascii_beq ch "5"
      || ascii_beq ch "6"
      || ascii_beq ch "7"
      || ascii_beq ch "8"
      || ascii_beq ch "9")%bool.

Definition is_oct_num (ch : ascii) : bool
  := match OctalString.ascii_to_digit ch with Some _ => true | None => false end.

Definition is_hex_num (ch : ascii) : bool
  := match HexString.ascii_to_digit ch with Some _ => true | None => false end.

Definition startswith_oct (s : string) : bool
  := match s with
     | String zero (String kind (String d rest))
       => ascii_beq zero "0" && ascii_beq kind "o" && is_oct_num d
     | _ => false
     end.

Definition startswith_hex (s : string) : bool
  := match s with
     | String zero (String kind (String d rest))
       => ascii_beq zero "0" && ascii_beq kind "x" && is_hex_num d
     | _ => false
     end.

Definition parse_bin_prefix : ParserAction _ := "0b".
Definition parse_oct_prefix : ParserAction _ := "0o".
Definition parse_dec_prefix : ParserAction _ := "".
Definition parse_hex_prefix : ParserAction _ := "0x".

Definition parse_digits_gen_step (base : N) : ParserAction N
  := (parse_strs
        (List.flat_map
           (fun v => if (v <? 10)%N
                     then [(String (ascii_of_N (v + N_of_ascii "0")) "", v)]
                     else [(String (ascii_of_N (v - 10 + N_of_ascii "A")) "", v);
                             (String (ascii_of_N (v - 10 + N_of_ascii "a")) "", v)])
           (List.map N.of_nat (List.seq 0 (N.to_nat base))))).


(*
Definition parse_oct_digits : ParserAction (list N)
  := Eval cbv -[ParserAction parse_alt_gen parse_impossible parse_str parse_star] in
      parse_digits_gen 8.
Definition parse_dec_digits : ParserAction (list N)
  := Eval cbv -[ParserAction parse_alt_gen parse_impossible parse_str parse_star] in
      parse_digits_gen 10.
Definition parse_hex_digits : ParserAction (list N)
  := Eval cbv -[ParserAction parse_alt_gen parse_impossible parse_str parse_star] in
      parse_digits_gen 16.
 *)

Definition digits_to_N (base : N) (digits : list N) : N
  := List.fold_left
       (fun so_far d => base * so_far + d)%N
       digits
       0%N.

Redirect "log" Check eq_refl : digits_to_N 10 [1;2;3;4;5;6]%N = 123456%N.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_N : N >-> Z.
Local Coercion inject_Z : Z >-> Q.
Definition parse_num_gen {P} (base : N) (parse_prefix : ParserAction P) : ParserAction Q
  := ((strip_whitespace_around "-")?)
       ;;->{ fun n v => if n:option _ then (-v)%Q else v }
       parse_prefix ;;->{ fun _ v => v }
       ((((parse_digits_gen_step base)* )
           ;;->{ fun ds decimals
                 => (digits_to_N base ds
                     + digits_to_N base decimals / base^List.length decimals)%Q }
           "." ;;->{ fun _ v => v }
           (parse_digits_gen_step base)* )
        || parse_map (digits_to_N base : _ -> Q) ((parse_digits_gen_step base)+)).

Definition parse_num : ParserAction Q
  := parse_num_gen 2 parse_bin_prefix
     || parse_num_gen 8 parse_oct_prefix
     || parse_num_gen 10 parse_dec_prefix
     || parse_num_gen 16 parse_hex_prefix.

Redirect "log" Check let ls := [("-1234", -(1234):Q); ("0xF", 15:Q); ("10.5", (10 + 5/10)); ("-10.5", -(10+5/10))]%Q in
                     eq_refl
                     : List.map (fun '(s, v) => ((parse_num;;->{fun v _ => v} ε)%parse s )) ls
                       = List.map (fun '(s, v) => [(v, "")]) ls.

Inductive Qexpr := Qv (_ : Q) | Qeopp (a : Qexpr) | Qeadd (a b : Qexpr) | Qesub (a b : Qexpr) | Qemul (a b : Qexpr) | Qediv (a b : Qexpr) | Qepow (b e : Qexpr).
Coercion Qv : Q >-> Qexpr.
Delimit Scope Qexpr_scope with Qexpr.
Bind Scope Qexpr_scope with Qexpr.
Infix "^" := Qepow : Qexpr_scope.
Infix "*" := Qemul : Qexpr_scope.
Infix "+" := Qeadd : Qexpr_scope.
Infix "/" := Qediv : Qexpr_scope.
Infix "-" := Qesub : Qexpr_scope.
Notation "- x" := (Qeopp x) : Qexpr_scope.

Fixpoint eval_Qexpr (v : Qexpr) : Q
  := match v with
     | Qv x => x
     | Qeopp a => Qopp (eval_Qexpr a)
     | Qeadd a b => Qplus (eval_Qexpr a) (eval_Qexpr b)
     | Qesub a b => Qminus (eval_Qexpr a) (eval_Qexpr b)
     | Qemul a b => Qmult (eval_Qexpr a) (eval_Qexpr b)
     | Qediv a b => Qdiv (eval_Qexpr a) (eval_Qexpr b)
     | Qepow b e => let b := eval_Qexpr b in
                    let e := eval_Qexpr e in
                    let (qe, re) := Z.div_eucl (Qnum e) (Z.pos (Qden e)) in
                    (* (b^qe)*(b^(re/Qden e)) *)
                    Qmult (Qpower b qe) (Qpower b (* approximate *) (re / Z.pos (Qden e)))
     end.

Fixpoint eval_Qexpr_strict (v : Qexpr) : option Q
  := match v with
     | Qv x => Some x
     | Qeopp a => option_map Qopp (eval_Qexpr_strict a)
     | Qeadd a b => a <- eval_Qexpr_strict a; b <- eval_Qexpr_strict b; Some (Qplus a b)
     | Qesub a b => a <- eval_Qexpr_strict a; b <- eval_Qexpr_strict b; Some (Qminus a b)
     | Qemul a b => a <- eval_Qexpr_strict a; b <- eval_Qexpr_strict b; Some (Qmult a b)
     | Qediv a b => a <- eval_Qexpr_strict a; b <- eval_Qexpr_strict b; Some (Qdiv a b)
     | Qepow b e => b <- eval_Qexpr_strict b;
                      e <- eval_Qexpr_strict e;
                      let (qe, re) := Z.div_eucl (Qnum e) (Z.pos (Qden e)) in
                      if Z.eqb re 0
                      then Some (Qpower b qe)
                      else None
     end.

Definition parse_ops {A} (ls : list (string * (A -> A -> A))) (parse : ParserAction A) : ParserAction A
  := parse ;;->{fun l fs => List.fold_left (fun v f => f v) fs l}
           (strip_whitespace_around (parse_strs ls) ;;->{fun f r l => f l r}
                                    parse)*.

Section step.
  Context (parse : ParserAction Qexpr).

  Definition parseQexpr_gen_parens : ParserAction Qexpr
    := ("(" ;;->{fun _ v => v} strip_whitespace_around parse ;;->{fun v _ => v} ")")
       || parse_map Qv parse_num.
  Definition parseQexpr_gen_exp : ParserAction Qexpr
    := parse_ops [("^", Qepow)] parseQexpr_gen_parens.
  Definition parseQexpr_gen_mul_div : ParserAction Qexpr
    := parse_ops [("*", Qemul); ("/", Qediv)] parseQexpr_gen_exp.
  Definition parseQexpr_gen_add_sub : ParserAction Qexpr
    := parse_ops [("+", Qeadd); ("-", Qesub)] parseQexpr_gen_mul_div.
End step.

Fixpoint parse_Qexpr_fueled (fuel : nat) : ParserAction Qexpr
  := strip_whitespace_around
       (parseQexpr_gen_add_sub (match fuel with
                                | O => parse_impossible
                                | S fuel => parse_Qexpr_fueled fuel
                                end)).

Definition parse_Qexpr : ParserAction Qexpr := fuel parse_Qexpr_fueled.

Definition parseQexpr_arith (s : string) : option Qexpr
  := finalize parse_Qexpr s.
Definition parseQ_arith (s : string) : option Q
  := option_map eval_Qexpr (parseQexpr_arith s).
Definition parseZ_arith (s : string) : option Z
  := (q <- parseQ_arith s; Some (Qnum q / Z.pos (Qden q)))%Z%option.
Definition parsepositive_arith (s : string) : option positive
  := (z <- parseZ_arith s; match z with Z0 => None | Zpos p => Some p | Zneg _ => None end).
Definition parseN_arith (s : string) : option N
  := (z <- parseZ_arith s; match z with Z0 => Some 0 | Zpos p => Some (Npos p) | Zneg _ => None end)%N%option.
Definition parsenat_arith (s : string) : option nat
  := (n <- parseN_arith s; Some (N.to_nat n)).

Definition Q_to_Z_strict (x : Q) : option Z
  := let '(q, r) := Z.div_eucl (Qnum x) (Zpos (Qden x)) in
     if Z.eqb r 0
     then Some q
     else None.

Definition parseQ_arith_strict (s : string) : option Q
  := (q <- parseQexpr_arith s; eval_Qexpr_strict q)%option.
Definition parseZ_arith_strict (s : string) : option Z
  := (q <- parseQ_arith_strict s; Q_to_Z_strict q)%option.
Definition parsepositive_arith_strict (s : string) : option positive
  := (z <- parseZ_arith_strict s; match z with Z0 => None | Zpos p => Some p | Zneg _ => None end).
Definition parseN_arith_strict (s : string) : option N
  := (z <- parseZ_arith_strict s; match z with Z0 => Some 0 | Zpos p => Some (Npos p) | Zneg _ => None end)%N%option.
Definition parsenat_arith_strict (s : string) : option nat
  := (n <- parseN_arith_strict s; Some (N.to_nat n)).
