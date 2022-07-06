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
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ListUtil.GroupAllBy.
Require Import Crypto.Util.Notations.
Import ListNotations.
Import BinPosDef.
Local Set Implicit Arguments.
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

Inductive Qexpr_poly {var : Type} := Qvar (v : var) | Qv (_ : Q) | Qeopp (a : Qexpr_poly) | Qeadd (a b : Qexpr_poly) | Qesub (a b : Qexpr_poly) | Qemul (a b : Qexpr_poly) | Qediv (a b : Qexpr_poly) | Qepow (b e : Qexpr_poly).
Global Arguments Qexpr_poly var : clear implicits.
Declare Scope Qexpr_scope.
Delimit Scope Qexpr_scope with Qexpr.
Bind Scope Qexpr_scope with Qexpr_poly.
Infix "^" := Qepow : Qexpr_scope.
Infix "*" := Qemul : Qexpr_scope.
Infix "+" := Qeadd : Qexpr_scope.
Infix "/" := Qediv : Qexpr_scope.
Infix "-" := Qesub : Qexpr_scope.
Notation "- x" := (Qeopp x) : Qexpr_scope.
Notation Qexpr := (@Qexpr_poly Empty_set).
Coercion QvQ (x : Q) : Qexpr := Qv x.

Definition monomial_in T var := (T * (var * Z) * list (var * Z (* approximate exponent *)))%type.
Definition poly_in T var := (T * list (monomial_in T var))%type.
Definition reduce_monomial {T var} (var_beq : var -> var -> bool) (m : monomial_in T var) : T + monomial_in T var
  := let '(c, v, vs) := m in
     let vs := List.groupAllBy (fun '(v, _) '(v', _) => var_beq v v') (v :: vs) in
     match Option.List.map
             (fun vs
              => match vs with
                 | [] => None
                 | (v, _) :: _
                   => let e := fold_right Z.add 0%Z (List.map snd vs) in
                      if (Z.eqb e 0)
                      then None
                      else Some (v, e)
                 end)
             vs with
     | [] => inl c
     | v :: vs => inr (c, v, vs)
     end.
Definition const_poly {T var} (v : T) : poly_in T var := (v, []).
Definition var_monomial {T var} (one : T) (v : var) : monomial_in T var := (one, (v, 1%Z), []).
Definition var_poly {T var} (zero : T) (one : T) (v : var) : poly_in T var := (zero, [var_monomial one v]).
Definition add_poly {T var} (addT : T -> T -> T) (p1 p2 : poly_in T var) : poly_in T var
  := let '(c1, p1) := p1 in
     let '(c2, p2) := p2 in
     (addT c1 c2, p1 ++ p2)%list.
Definition mul_monomial {T var} (mulT : T -> T -> T) (m1 m2 : monomial_in T var) : monomial_in T var
  := let '(coef1, (v1, e1), vs1) := m1 in
     let '(coef2, (v2, e2), vs2) := m2 in
     (mulT coef1 coef2, (v1, e1), vs1 ++ (v2, e2) :: vs2)%list.
Definition scmul_monomial {T var} (mulT : T -> T -> T) (sc : T) (m : monomial_in T var) : monomial_in T var
  := let '(coef, (v, e), vs) := m in
     (mulT sc coef, (v, e), vs).
Definition mul_poly {T var} (addT : T -> T -> T) (mulT : T -> T -> T) (p1 p2 : poly_in T var) : poly_in T var
  := let '(c1, p1) := p1 in
     let '(c2, p2) := p2 in
     (mulT c1 c2, List.map (scmul_monomial mulT c1) p2 ++ List.map (scmul_monomial mulT c2) p1 ++ List.flat_map (fun p => List.map (mul_monomial mulT p) p2) p1)%list.
Definition pow_monomial {T var} (powT : T -> Z -> T) (m : monomial_in T var) (e : Z) : monomial_in T var
  := let '(coef, (v, ev), vs) := m in
     (powT coef e, (v, ev + e), List.map (fun '(v, ev) => (v, ev + e)) vs)%Z.
Definition pow_monomial_strict {T var} (powT : T -> Z -> option T) (m : monomial_in T var) (e : Z) : option (monomial_in T var)
  := let '(coef, (v, ev), vs) := m in
     (coef <- powT coef e;
      Some (coef, (v, ev + e), List.map (fun '(v, ev) => (v, ev + e)) vs))%Z%option.
Definition pow_poly {T var} (addT : T -> T -> T) (mulT : T -> T -> T) (powT : T -> Z -> T) (one : T) (p : poly_in T var) (e : Z) : poly_in T var
  := match p with
     | (c, []) => (powT c e, [])
     | (c, _)
       => match e with
          | Z.neg _ => (powT c e, []) (* approximate *)
          | Z0 => (one, [])
          | Z.pos e => BinPos.Pos.iter (mul_poly addT mulT p) (const_poly one) e
          end
     end.
Definition pow_poly_strict {T var} (addT : T -> T -> T) (mulT : T -> T -> T) (powT : T -> Z -> option T) (one : T) (p : poly_in T var) (e : Z) : option (poly_in T var)
  := match p with
     | (c, []) => c <- powT c e; Some (c, [])
     | (c, _)
       => match e with
          | Z.neg _ => None
          | Z0 => Some (one, [])
          | Z.pos e => Some (BinPos.Pos.iter (mul_poly addT mulT p) (const_poly one) e)
          end
end%option.
Definition monomial_var_part_beq {T var} (var_beq : var -> var -> bool) (m1 m2 : monomial_in T var) : bool
  := match reduce_monomial var_beq (mul_monomial (fun a _ => a) m1 (pow_monomial (fun a _ => a) m2 (-1))) with
     | inl _ => true (* the var parts cancel, and we have only a constant part *)
     | inr _ => false (* var parts don't cancel, so must be different *)
     end.
Definition reduce_poly {T var} (var_beq : var -> var -> bool) (T_zero_beq : T -> bool) (reduceT : T -> T) (addT : T -> T -> T) (p : poly_in T var) : poly_in T var
  := let '(c, vs) := p in
     let vs := List.map (reduce_monomial var_beq) vs in
     let cs := Option.List.map (fun v => match v with inl v => Some v | inr _ => None end) vs in
     let vs := Option.List.map (fun v => match v with inr v => Some v | inl _ => None end) vs in
     let c := fold_right addT c cs in
     let vs := List.groupAllBy (monomial_var_part_beq var_beq) vs in
     (reduceT c,
       Option.List.map
         (fun vs
          => match vs with
             | [] => None
             | (c, v0, v0s) :: vs
               => let c := reduceT (fold_right addT c (List.map (fun '(c, _, _) => c) vs)) in
                  if T_zero_beq c
                  then None
                  else Some (c, v0, v0s)
             end)
         vs).

Definition reduce_Qpoly {var} (var_beq : var -> var -> bool) : poly_in Q var -> poly_in Q var
  := reduce_poly var_beq (Qeq_bool 0) Qred Qplus.

Local Notation add_Qpoly := (add_poly Qplus).
Local Notation mul_Qpoly := (mul_poly Qplus Qmult).
Local Notation pow_Qpoly := (pow_poly Qplus Qmult Qpower 1%Q).
Local Notation pow_Qpoly_strict := (pow_poly_strict Qplus Qmult (fun x y => if andb (Qeq_bool x 0) (Z.leb y 0) then None else Some (Qpower x y)) 1%Q).
Local Notation opp_Qpoly := (mul_Qpoly (const_poly (-1)%Q)).
Local Notation sub_Qpoly a b := (add_Qpoly a (opp_Qpoly b)).

Definition poly_coef_map {T1 T2 var} (f : T1 -> T2) (p : poly_in T1 var) : poly_in T2 var
  := let '(c, vs) := p in
     (f c, List.map (fun '(c, v, vs) => (f c, v, vs)) vs).

Definition poly_coef_map_strict {T1 T2 var} (f : T1 -> option T2) (p : poly_in T1 var) : option (poly_in T2 var)
  := let '(c, vs) := p in
     (c <- f c;
      vs <-- List.map (fun '(c, v, vs) => c <- f c; Some (c, v, vs)) vs;
      Some (c, vs))%option.

Fixpoint eval_Qexpr_poly {var} (v : Qexpr_poly var) : poly_in Q var
  := match v with
     | Qvar v => var_poly 0 1 v
     | Qv x => const_poly x
     | Qeopp a => opp_Qpoly (eval_Qexpr_poly a)
     | Qeadd a b => add_Qpoly (eval_Qexpr_poly a) (eval_Qexpr_poly b)
     | Qesub a b => sub_Qpoly (eval_Qexpr_poly a) (eval_Qexpr_poly b)
     | Qemul a b => mul_Qpoly (eval_Qexpr_poly a) (eval_Qexpr_poly b)
     | Qediv a b => mul_Qpoly (eval_Qexpr_poly a) (pow_Qpoly (eval_Qexpr_poly b) (-1))
     | Qepow b e => let b := eval_Qexpr_poly b in
                    let '(e, _) := eval_Qexpr_poly e in
                    let (qe, re) := Z.div_eucl (Qnum e) (Z.pos (Qden e)) in
                    (* (b^qe)*(b^(re/Qden e)) *)
                    mul_Qpoly (pow_Qpoly b qe) (pow_Qpoly b (* approximate *) (re / Z.pos (Qden e)))
     end%Q.

Definition eval_Qexpr (v : Qexpr) : Q
  := match eval_Qexpr_poly v with
     | (c, []) => c
     | (c, (_, (v, _), _)::_) => match v with end
     end.

Fixpoint eval_Qexpr_poly_strict {var} (v : Qexpr_poly var) : option (poly_in Q var)
  := match v with
     | Qvar v => Some (var_poly 0%Q 1%Q v)
     | Qv x => Some (const_poly x)
     | Qeopp a => option_map opp_Qpoly (eval_Qexpr_poly_strict a)
     | Qeadd a b => (a <- eval_Qexpr_poly_strict a; b <- eval_Qexpr_poly_strict b; Some (add_Qpoly a b))
     | Qesub a b => (a <- eval_Qexpr_poly_strict a; b <- eval_Qexpr_poly_strict b; Some (sub_Qpoly a b))
     | Qemul a b => (a <- eval_Qexpr_poly_strict a; b <- eval_Qexpr_poly_strict b; Some (mul_Qpoly a b))
     | Qediv a b => (a <- eval_Qexpr_poly_strict a;
                     b <- eval_Qexpr_poly_strict b;
                     b <- pow_Qpoly_strict b (-1);
                     Some (mul_Qpoly a b))
     | Qepow b e => (b <- eval_Qexpr_poly_strict b;
                     e <- eval_Qexpr_poly_strict e;
                     match e with
                     | (_, _::_) => None
                     | (e, [])
                       => let (qe, re) := Z.div_eucl (Qnum e) (Z.pos (Qden e)) in
                          if Z.eqb re 0
                          then pow_Qpoly_strict b qe
                          else None
                     end)
     end.

Definition eval_Qexpr_strict (v : Qexpr) : option Q
  := match eval_Qexpr_poly_strict v with
     | Some (c, []) => Some c
     | Some (c, (_, (v, _), _)::_) => match v with end
     | None => None
     end.

Definition eval_Qexpr_poly_reduced {var} (var_beq : var -> var -> bool) (v : Qexpr_poly var) : poly_in Q var
  := reduce_Qpoly var_beq (eval_Qexpr_poly v).

Definition eval_Qexpr_poly_reduced_strict {var} (var_beq : var -> var -> bool) (v : Qexpr_poly var) : option (poly_in Q var)
  := option_map (reduce_Qpoly var_beq) (eval_Qexpr_poly_strict v).

Definition parse_ops {A} (ls : list (string * (A -> A -> A))) (parse : ParserAction A) : ParserAction A
  := parse ;;->{fun l fs => List.fold_left (fun v f => f v) fs l}
           (strip_whitespace_around (parse_strs ls) ;;->{fun f r l => f l r}
                                    parse)*.

Definition parse_prefix_ops {A} (ls : list (string * (A -> A))) (parse : ParserAction A) : ParserAction A
  := ((strip_whitespace_after (parse_strs ls))* )
       ;;->{fun ls v => fold_right (fun f x => f x) v ls }
       parse.

Section step.
  Context {var : Type}
          (parse_num : ParserAction Q)
          (parse_var : ParserAction var).
  Local Notation Qexpr_poly := (Qexpr_poly var).
  Context (parse : ParserAction Qexpr_poly).

  Definition parseQexpr_poly_gen_parens : ParserAction Qexpr_poly
    := ("(" ;;->{fun _ v => v} strip_whitespace_around parse ;;->{fun v _ => v} ")")
       || parse_map Qv parse_num
       || parse_map Qvar parse_var.
  Definition parseQexpr_poly_gen_exp : ParserAction Qexpr_poly
    := parse_ops [("^", Qepow)] parseQexpr_poly_gen_parens.
  Definition parseQexpr_poly_gen_opp : ParserAction Qexpr_poly
    := parse_prefix_ops [("-", Qeopp)] parseQexpr_poly_gen_exp.
  Definition parseQexpr_poly_gen_mul_div : ParserAction Qexpr_poly
    := parse_ops [("*", Qemul); ("/", Qediv)] parseQexpr_poly_gen_opp.
  Definition parseQexpr_poly_gen_add_sub : ParserAction Qexpr_poly
    := parse_ops [("+", Qeadd); ("-", Qesub)] parseQexpr_poly_gen_mul_div.
End step.

Fixpoint parse_Qexpr_poly_fueled {var} (parse_num : ParserAction Q) (parse_var : ParserAction var) (fuel : nat) : ParserAction (Qexpr_poly var)
  := strip_whitespace_around
       (parseQexpr_poly_gen_add_sub
          parse_num
          parse_var
          (match fuel with
           | O => parse_impossible
           | S fuel => parse_Qexpr_poly_fueled parse_num parse_var fuel
           end)).

Definition parse_Qexpr_poly_gen {var} (parse_num : ParserAction Q) (parse_var : ParserAction var) : ParserAction (Qexpr_poly var) := fuel (parse_Qexpr_poly_fueled parse_num parse_var).

Definition parse_Qexpr_gen (parse_num : ParserAction Q) : ParserAction Qexpr := parse_Qexpr_poly_gen parse_num parse_impossible.

Definition parse_Qexpr_poly {var} (parse_var : ParserAction var) : ParserAction (Qexpr_poly var) := parse_Qexpr_poly_gen (parse_num false) parse_var.

Definition parse_Qexpr_with_vars (vars : list (string * Q)) : ParserAction Qexpr
  := parse_Qexpr_poly_gen
       (List.fold_right
          (fun '((s, q) : string * Q) default => default || parse_map (fun _ => q) s)%parse
          (parse_num false)
          vars)
       parse_impossible.

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

Section with_var.
  Context {var : Type}
          (var_beq : var -> var -> bool)
          (parse_var : ParserAction var).

  Definition parse_Q_with_vars (vars : list (string * Q)) : ParserAction Q
    := parse_map eval_Qexpr (parse_Qexpr_with_vars vars).
  Definition parse_Q_strict_with_vars (vars : list (string * Q)) : ParserAction Q
    := parse_option_list_map eval_Qexpr_strict (parse_Qexpr_with_vars vars).
  Definition parse_Q_poly : ParserAction (poly_in Q var)
    := parse_map (eval_Qexpr_poly_reduced var_beq) (parse_Qexpr_poly parse_var).
  Definition parse_Q_poly_strict : ParserAction (poly_in Q var)
    := parse_option_list_map (eval_Qexpr_poly_reduced_strict var_beq) (parse_Qexpr_poly parse_var).
  Definition parse_Z_with_vars (vars : list (string * Q)) : ParserAction Z
    := parse_map Q_to_Z (parse_Q_with_vars vars).
  Definition parse_Z_strict_with_vars (vars : list (string * Q)) : ParserAction Z
    := parse_option_list_map Q_to_Z_strict (parse_Q_strict_with_vars vars).
  Definition parse_Z_poly : ParserAction (poly_in Z var)
    := parse_map (poly_coef_map Q_to_Z) parse_Q_poly.
  Definition parse_Z_poly_strict : ParserAction (poly_in Z var)
    := parse_option_list_map (poly_coef_map_strict Q_to_Z_strict) parse_Q_poly_strict.
  Definition parse_N_with_vars (vars : list (string * Q)) : ParserAction N
    := parse_map Z.to_N (parse_Z_with_vars vars).
  Definition parse_N_strict_with_vars (vars : list (string * Q)) : ParserAction N
    := parse_option_list_map N_of_Z_strict (parse_Z_strict_with_vars vars).
  Definition parse_N_poly : ParserAction (poly_in N var)
    := parse_map (poly_coef_map Z.to_N) parse_Z_poly.
  Definition parse_N_poly_strict : ParserAction (poly_in N var)
    := parse_option_list_map (poly_coef_map_strict N_of_Z_strict) parse_Z_poly_strict.
  Definition parse_nat_with_vars (vars : list (string * Q)) : ParserAction nat
    := parse_map N.to_nat (parse_N_with_vars vars).
  Definition parse_nat_strict_with_vars (vars : list (string * Q)) : ParserAction nat
    := parse_map N.to_nat (parse_N_strict_with_vars vars).
  Definition parse_nat_poly : ParserAction (poly_in nat var)
    := parse_map (poly_coef_map N.to_nat) parse_N_poly.
  Definition parse_nat_poly_strict : ParserAction (poly_in nat var)
    := parse_map (poly_coef_map N.to_nat) parse_N_poly_strict.
  Definition parse_positive_with_vars (vars : list (string * Q)) : ParserAction positive
    := parse_map positive_of_N (parse_N_with_vars vars).
  Definition parse_positive_strict_with_vars (vars : list (string * Q)) : ParserAction positive
    := parse_option_list_map positive_of_N_strict (parse_N_strict_with_vars vars).
  Definition parse_positive_poly : ParserAction (poly_in positive var)
    := parse_map (poly_coef_map positive_of_N) parse_N_poly.
  Definition parse_positive_poly_strict : ParserAction (poly_in positive var)
    := parse_option_list_map (poly_coef_map_strict positive_of_N_strict) parse_N_poly_strict.

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

  Definition parseQexpr_poly_arith (s : string) : option (Qexpr_poly var)
    := finalize (parse_Qexpr_poly parse_var) s.
  Definition parseQ_poly_arith (s : string) : option (poly_in Q var)
    := option_map (eval_Qexpr_poly_reduced var_beq) (parseQexpr_poly_arith s).
  Definition parseZ_poly_arith (s : string) : option (poly_in Z var)
    := (q <- parseQ_poly_arith s; Some (poly_coef_map (fun q => (Qnum q / Z.pos (Qden q))%Z) q))%option.
  Definition parsepositive_poly_arith (s : string) : option (poly_in positive var)
    := (z <- parseZ_poly_arith s; poly_coef_map_strict (fun z => match z with Z0 => None | Zpos p => Some p | Zneg _ => None end) z).
  Definition parseN_poly_arith (s : string) : option (poly_in N var)
    := (z <- parseZ_poly_arith s; poly_coef_map_strict (fun z => match z with Z0 => Some 0 | Zpos p => Some (Npos p) | Zneg _ => None end)%N z)%option.
  Definition parsenat_poly_arith (s : string) : option (poly_in nat var)
    := (n <- parseN_poly_arith s; Some (poly_coef_map N.to_nat n)).

  Definition parseQ_poly_arith_strict (s : string) : option (poly_in Q var)
    := (q <- parseQexpr_poly_arith s; eval_Qexpr_poly_strict q)%option.
  Definition parseZ_poly_arith_strict (s : string) : option (poly_in Z var)
    := (q <- parseQ_poly_arith_strict s; poly_coef_map_strict Q_to_Z_strict q)%option.
  Definition parsepositive_poly_arith_strict (s : string) : option (poly_in positive var)
    := (z <- parseZ_poly_arith_strict s; poly_coef_map_strict (fun z => match z with Z0 => None | Zpos p => Some p | Zneg _ => None end) z).
  Definition parseN_poly_arith_strict (s : string) : option (poly_in N var)
    := (z <- parseZ_poly_arith_strict s; poly_coef_map_strict (fun z => match z with Z0 => Some 0 | Zpos p => Some (Npos p) | Zneg _ => None end)%N z)%option.
  Definition parsenat_poly_arith_strict (s : string) : option (poly_in nat var)
    := (n <- parseN_poly_arith_strict s; Some (poly_coef_map N.to_nat n)).

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
End with_var.

Redirect "log" Check eq_refl : parseQexpr_arith "1 + -2" = Some (1%Q + - 2%Q)%Qexpr.
Redirect "log" Check eq_refl : parseQ_poly_arith String.eqb "x" "(5 * x + 3 * x^2 + 10)/2" = Some (5, [(5 / 2, ("x", 1%Z), []); (3 / 2, ("x", 2%Z), [])])%Q.
