Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Option.
Require Coq.Strings.BinaryString.
Require Coq.Strings.OctalString.
Require Coq.Strings.HexString.
Require Import Crypto.Util.Strings.Decimal.
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
  := match DecimalString.uint_of_char ch (Some Decimal.Nil) with Some _ => true | None => false end.

Definition is_oct_num (ch : ascii) : bool
  := match OctalString.ascii_to_digit ch with Some _ => true | None => false end.

Definition is_hex_num (ch : ascii) : bool
  := match HexString.ascii_to_digit ch with Some _ => true | None => false end.

Definition startswith_oct (s : string) : bool
  := match s with
     | String zero (String kind (String d rest))
       => (zero =? "0")%char && (kind =? "o")%char && is_oct_num d
     | _ => false
     end.

Definition startswith_hex (s : string) : bool
  := match s with
     | String zero (String kind (String d rest))
       => (zero =? "0")%char && (kind =? "x")%char && is_hex_num d
     | _ => false
     end.

Definition parse_bin_prefix : ParserAction _ := "0b".
Definition parse_oct_prefix : ParserAction _ := "0o".
Definition parse_dec_prefix : ParserAction _ := "".
Definition parse_hex_prefix : ParserAction _ := "0x".
Definition parse_hex_postfix : ParserAction _ := "h".

(** Is [E]/[e] a valid digit in the given base? *)
Definition base_accepts_E (base : N) : bool
  := (10 + N_of_ascii "E" - N_of_ascii "A" <? base)%N.

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

Definition parse_N_digits (base : N) : ParserAction N
  := (parse_map (digits_to_N base) ((parse_digits_gen_step base)+)).

Definition parse_num_gen {P P'} (allow_neg : bool) (base : N) (parse_prefix : option (ParserAction P)) (parse_postfix : option (ParserAction P'))  : ParserAction Q
  := (let parse_E_exponent
        := (("e" || "E") ;;->{ fun _ v => Qpower 10 v }
                         (((strip_whitespace_after "-")?)
                            ;;->{ fun n (v:N) => if n:option _ then (-v)%Z else v }
                            (parse_N_digits base)))%parse in
      let parse_P_exponent
        := (("p" || "P") ;;->{ fun _ v => Qpower 2 v }
                         (((strip_whitespace_after "-")?)
                            ;;->{ fun n (v:N) => if n:option _ then (-v)%Z else v }
                            (parse_N_digits base)))%parse in
      (if allow_neg then ((strip_whitespace_after "-")?) else parse_map (fun _ => None) "")
        ;;->{ fun n v => if n:option _ then (-v)%Q else v }
        let parse_main
          := let parse_main_digits := (parse_digits_gen_step base)* in
             (((match parse_prefix with
                | Some _ => parse_main_digits
                | None => parse_digits_gen_step (N.min 10 base) ;;->{cons} parse_main_digits
                end)
                 ;;->{ fun ds decimals
                       => (digits_to_N base ds
                           + digits_to_N base decimals / base^List.length decimals)%Q }
                 "." ;;R
                         (parse_digits_gen_step base)* )
              || parse_map (digits_to_N base : _ -> Q) ((parse_digits_gen_step base)+))
               ;;->{ fun n e => match e with Some e => n * e | None => n end%Q }
               ((if base_accepts_E base
                 then parse_P_exponent (* if [e] is a valid character in the base, then we don't permit [e] as an exponent *)
                 else (parse_E_exponent || parse_P_exponent))?) in
        match parse_prefix, parse_postfix with
        | None, None => parse_main
        | Some parse_prefix, None => parse_prefix ;;R parse_main
        | Some parse_prefix, Some parse_postfix => parse_prefix ;;R parse_main ;;L parse_postfix
        | None, Some parse_postfix => parse_main ;;L parse_postfix
        end)%parse.

Definition parse_num_gen_prefix {P} (allow_neg : bool) (base : N) (parse_prefix : ParserAction P) : ParserAction Q
  := @parse_num_gen P unit allow_neg base (Some parse_prefix) None.
Definition parse_num_gen_postfix {P} (allow_neg : bool) (base : N) (parse_postfix : ParserAction P) : ParserAction Q
  := @parse_num_gen unit P allow_neg base None (Some parse_postfix).

Definition parse_num (allow_neg : bool) : ParserAction Q
  := parse_num_gen_prefix allow_neg 2 parse_bin_prefix
     || parse_num_gen_prefix allow_neg 8 parse_oct_prefix
     || parse_num_gen_prefix allow_neg 10 parse_dec_prefix
     || parse_num_gen_prefix allow_neg 16 parse_hex_prefix
     || parse_num_gen_postfix allow_neg 16 parse_hex_postfix.

Definition parse_int_gen {P P'} (allow_neg : bool) (base : N) (parse_prefix : option (ParserAction P)) (parse_postfix : option (ParserAction P')) : ParserAction Z
  := (let parse_E_exponent
        := (("e" || "E") ;;->{ fun _ (v:N) => Z.pow 10 v } (parse_N_digits base))%parse in
      let parse_P_exponent
        := (("p" || "P") ;;->{ fun _ (v:N) => Z.pow 2 v } (parse_N_digits base))%parse in
      (if allow_neg then ((strip_whitespace_after "-")?) else parse_map (fun _ => None) "")
        ;;->{ fun n v => if n:option _ then (-v)%Z else v }
        let parse_main
          := let parse_main_digits := (parse_digits_gen_step base)* in
             (parse_map
                (digits_to_N base)
                match parse_prefix with
                | Some _ => parse_main_digits
                | None => parse_digits_gen_step (N.min 10 base) ;;->{cons} parse_main_digits
                end)
               ;;->{ fun (n:N) e => match e with Some e => n * e | None => n end%Z }
               ((if base_accepts_E base
                 then parse_P_exponent (* if [e] is a valid character in the base, then we don't permit [e] as an exponent *)
                 else (parse_E_exponent || parse_P_exponent))?) in
        match parse_prefix, parse_postfix with
        | None, None => parse_main
        | Some parse_prefix, None => parse_prefix ;;R parse_main
        | Some parse_prefix, Some parse_postfix => parse_prefix ;;R parse_main ;;L parse_postfix
        | None, Some parse_postfix => parse_main ;;L parse_postfix
        end)%parse.

Definition parse_int_gen_prefix {P} (allow_neg : bool) (base : N) (parse_prefix : ParserAction P) : ParserAction Z
  := @parse_int_gen P unit allow_neg base (Some parse_prefix) None.
Definition parse_int_gen_postfix {P} (allow_neg : bool) (base : N) (parse_postfix : ParserAction P) : ParserAction Z
  := @parse_int_gen unit P allow_neg base None (Some parse_postfix).

Definition parse_int (allow_neg : bool) : ParserAction Z
  := parse_int_gen_prefix allow_neg 2 parse_bin_prefix
     || parse_int_gen_prefix allow_neg 8 parse_oct_prefix
     || parse_int_gen_prefix allow_neg 10 parse_dec_prefix
     || parse_int_gen_prefix allow_neg 16 parse_hex_prefix
     || parse_int_gen_postfix allow_neg 16 parse_hex_postfix.

Redirect "log" Check let ls := [("-1234", -(1234):Q); ("0xF", 15:Q); ("10.5", (10 + 5/10)); ("-10.5", -(10+5/10))]%Q in
                     eq_refl
                     : List.map (fun '(s, v) => ((parse_num true;;->{fun v _ => v} ε)%parse s )) ls
                       = List.map (fun '(s, v) => [(v, "")]) ls.

(* This was previously stack overflowing due to treating [e] as an exponent *)
Redirect "log" Compute parse_num false "0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551".

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
     | Qediv a b => a <- eval_Qexpr_strict a; b <- eval_Qexpr_strict b; if Qeq_bool b 0 then None else Some (Qdiv a b)
     | Qepow b e => b <- eval_Qexpr_strict b;
                      e <- eval_Qexpr_strict e;
                      let (qe, re) := Z.div_eucl (Qnum e) (Z.pos (Qden e)) in
                      if Z.eqb re 0 && (negb (Qeq_bool b 0) || Z.ltb 0 qe)
                      then Some (Qpower b qe)
                      else None
     end.

Definition parse_ops {A} (ls : list (string * (A -> A -> A))) (parse : ParserAction A) : ParserAction A
  := parse ;;->{fun l fs => List.fold_left (fun v f => f v) fs l}
           (strip_whitespace_around (parse_strs ls) ;;->{fun f r l => f l r}
                                    parse)*.

Definition parse_prefix_ops {A} (ls : list (string * (A -> A))) (parse : ParserAction A) : ParserAction A
  := ((strip_whitespace_after (parse_strs ls))* )
       ;;->{fun ls v => fold_right (fun f x => f x) v ls }
       parse.

Section step.
  Context (parse_num : ParserAction Q)
          (parse : ParserAction Qexpr).

  Definition parseQexpr_gen_parens : ParserAction Qexpr
    := ("(" ;;->{fun _ v => v} strip_whitespace_around parse ;;->{fun v _ => v} ")")
       || parse_map Qv parse_num.
  Definition parseQexpr_gen_exp : ParserAction Qexpr
    := parse_ops [("^", Qepow)] parseQexpr_gen_parens.
  Definition parseQexpr_gen_opp : ParserAction Qexpr
    := parse_prefix_ops [("-", Qeopp)] parseQexpr_gen_exp.
  Definition parseQexpr_gen_mul_div : ParserAction Qexpr
    := parse_ops [("*", Qemul); ("/", Qediv)] parseQexpr_gen_opp.
  Definition parseQexpr_gen_add_sub : ParserAction Qexpr
    := parse_ops [("+", Qeadd); ("-", Qesub)] parseQexpr_gen_mul_div.
End step.

Fixpoint parse_Qexpr_fueled (parse_num : ParserAction Q) (fuel : nat) : ParserAction Qexpr
  := strip_whitespace_around
       (parseQexpr_gen_add_sub parse_num
                               (match fuel with
                                | O => parse_impossible
                                | S fuel => parse_Qexpr_fueled parse_num fuel
                                end)).

Definition parse_Qexpr_gen (parse_num : ParserAction Q) : ParserAction Qexpr := fuel (parse_Qexpr_fueled parse_num).

Definition parse_Qexpr_with_vars (vars : list (string * Q)) : ParserAction Qexpr
  := parse_Qexpr_gen
       (List.fold_right
          (fun '((s, q) : string * Q) default => default || parse_map (fun _ => q) s)%parse
          (parse_num false)
          vars).

Definition Q_to_Z (q : Q) : Z := (Qnum q / Z.pos (Qden q))%Z.
Definition Q_to_Z_strict (x : Q) : option Z
  := let '(q, r) := Z.div_eucl (Qnum x) (Zpos (Qden x)) in
     if Z.eqb r 0
     then Some q
     else None.
Definition N_of_Z_strict (z : Z) : option N
  := match z with Z0 => Some N0 | Zpos p => Some (Npos p) | Zneg _ => None end.
Definition positive_of_N (n : N) : positive
  := match n with N0 => 1%positive | Npos p => p end.
Definition positive_of_N_strict (n : N) : option positive
  := match n with N0 => None | Npos p => Some p end.

Definition parse_Q_with_vars (vars : list (string * Q)) : ParserAction Q
  := parse_map eval_Qexpr (parse_Qexpr_with_vars vars).
Definition parse_Q_strict_with_vars (vars : list (string * Q)) : ParserAction Q
  := parse_option_list_map eval_Qexpr_strict (parse_Qexpr_with_vars vars).
Definition parse_Z_with_vars (vars : list (string * Q)) : ParserAction Z
  := parse_map Q_to_Z (parse_Q_with_vars vars).
Definition parse_Z_strict_with_vars (vars : list (string * Q)) : ParserAction Z
  := parse_option_list_map Q_to_Z_strict (parse_Q_strict_with_vars vars).
Definition parse_N_with_vars (vars : list (string * Q)) : ParserAction N
  := parse_map Z.to_N (parse_Z_with_vars vars).
Definition parse_N_strict_with_vars (vars : list (string * Q)) : ParserAction N
  := parse_option_list_map N_of_Z_strict (parse_Z_strict_with_vars vars).
Definition parse_nat_with_vars (vars : list (string * Q)) : ParserAction nat
  := parse_map N.to_nat (parse_N_with_vars vars).
Definition parse_nat_strict_with_vars (vars : list (string * Q)) : ParserAction nat
  := parse_map N.to_nat (parse_N_strict_with_vars vars).
Definition parse_positive_with_vars (vars : list (string * Q)) : ParserAction positive
  := parse_map positive_of_N (parse_N_with_vars vars).
Definition parse_positive_strict_with_vars (vars : list (string * Q)) : ParserAction positive
  := parse_option_list_map positive_of_N_strict (parse_N_strict_with_vars vars).

Definition parseQexpr_arith_with_vars (vars : list (string * Q)) (s : string) : option Qexpr
  := finalize (parse_Qexpr_with_vars vars) s.
Definition parseQ_arith_with_vars (vars : list (string * Q)) (s : string) : option Q
  := option_map eval_Qexpr (parseQexpr_arith_with_vars vars s).
Definition parseZ_arith_with_vars (vars : list (string * Q)) (s : string) : option Z
  := (q <- parseQ_arith_with_vars vars s; Some (Qnum q / Z.pos (Qden q)))%Z%option.
Definition parsepositive_arith_with_vars (vars : list (string * Q)) (s : string) : option positive
  := (z <- parseZ_arith_with_vars vars s; match z with Z0 => None | Zpos p => Some p | Zneg _ => None end).
Definition parseN_arith_with_vars (vars : list (string * Q)) (s : string) : option N
  := (z <- parseZ_arith_with_vars vars s; match z with Z0 => Some 0 | Zpos p => Some (Npos p) | Zneg _ => None end)%N%option.
Definition parsenat_arith_with_vars (vars : list (string * Q)) (s : string) : option nat
  := (n <- parseN_arith_with_vars vars s; Some (N.to_nat n)).

Definition parseQ_arith_strict_with_vars (vars : list (string * Q)) (s : string) : option Q
  := (q <- parseQexpr_arith_with_vars vars s; eval_Qexpr_strict q)%option.
Definition parseZ_arith_strict_with_vars (vars : list (string * Q)) (s : string) : option Z
  := (q <- parseQ_arith_strict_with_vars vars s; Q_to_Z_strict q)%option.
Definition parsepositive_arith_strict_with_vars (vars : list (string * Q)) (s : string) : option positive
  := (z <- parseZ_arith_strict_with_vars vars s; match z with Z0 => None | Zpos p => Some p | Zneg _ => None end).
Definition parseN_arith_strict_with_vars (vars : list (string * Q)) (s : string) : option N
  := (z <- parseZ_arith_strict_with_vars vars s; match z with Z0 => Some 0 | Zpos p => Some (Npos p) | Zneg _ => None end)%N%option.
Definition parsenat_arith_strict_with_vars (vars : list (string * Q)) (s : string) : option nat
  := (n <- parseN_arith_strict_with_vars vars s; Some (N.to_nat n)).

Definition parse_Qexpr := parse_Qexpr_with_vars [].
Definition parseQexpr_arith := parseQexpr_arith_with_vars [].
Definition parseQ_arith := parseQ_arith_with_vars [].
Definition parseZ_arith := parseZ_arith_with_vars [].
Definition parsepositive_arith := parsepositive_arith_with_vars [].
Definition parseN_arith := parseN_arith_with_vars [].
Definition parsenat_arith := parsenat_arith_with_vars [].
Definition parseQ_arith_strict := parseQ_arith_strict_with_vars [].
Definition parseZ_arith_strict := parseZ_arith_strict_with_vars [].
Definition parsepositive_arith_strict := parsepositive_arith_strict_with_vars [].
Definition parseN_arith_strict := parseN_arith_strict_with_vars [].
Definition parsenat_arith_strict := parsenat_arith_strict_with_vars [].

Definition parse_Q_arith := parse_Q_with_vars [].
Definition parse_Q_arith_strict := parse_Q_strict_with_vars [].
Definition parse_Z_arith := parse_Z_with_vars [].
Definition parse_Z_arith_strict := parse_Z_strict_with_vars [].
Definition parse_N_arith := parse_N_with_vars [].
Definition parse_N_arith_strict := parse_N_strict_with_vars [].
Definition parse_nat_arith := parse_nat_with_vars [].
Definition parse_nat_arith_strict := parse_nat_strict_with_vars [].
Definition parse_positive_arith := parse_positive_with_vars [].
Definition parse_positive_arith_strict := parse_positive_strict_with_vars [].

Redirect "log" Check eq_refl : parseQexpr_arith "1 + -2" = Some (1%Q + - 2%Q)%Qexpr.
