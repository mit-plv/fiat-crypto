Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.Strings.Decimal.
Require Crypto.Util.Strings.OctalString.
Require Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Notations.
Import ListNotations.
Import BinPosDef.
Local Open Scope option_scope.
Local Open Scope list_scope.
Local Open Scope char_scope.
Local Open Scope string_scope.

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

Fixpoint split_before_first (f : ascii -> bool) (s : string) : string * string
  := match s with
     | EmptyString => (EmptyString, EmptyString)
     | String ch rest
       => if f ch
          then (EmptyString, s)
          else let '(s1, s2) := split_before_first f rest in
               (String ch s1, s2)
     end.

Fixpoint split_before_first_skip (f : ascii -> bool) (s : string) (skip : nat) : string * string
  := match skip, s with
     | 0, _ => split_before_first f s
     | _, EmptyString => (EmptyString, EmptyString)
     | S skip', String ch rest
       => let '(s1, s2) := split_before_first_skip f rest skip' in
          (String ch s1, s2)
     end.

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

Definition parse_N (s : string) : option (N * string)
  := if startswith_oct s
     then
       let '(n, rest) := split_before_first_skip (fun ch => negb (is_oct_num ch)) s 2 in
       Some (OctalString.to_N n, rest)
     else if startswith_hex s
          then
            let '(n, rest) := split_before_first_skip (fun ch => negb (is_hex_num ch)) s 2 in
            Some (HexString.to_N n, rest)
          else
            let '(n, rest) := split_before_first (fun ch => negb (is_num ch)) s in
            match Z_of_decimal_string n, Nat.eqb (String.length n) 0 with
            | Zneg _, _ | _, true => None
            | Z0, _ => Some (N0, rest)
            | Zpos p, _ => Some (Npos p, rest)
            end.

Definition parse_ch {T} (ls : list (ascii * T)) (s : string) : option (T * string)
  := match s with
     | EmptyString => None
     | String ch s
       => List.fold_right
            (fun '(ch', t) default
             => if ascii_beq ch ch' then Some (t, s) else default)
            None
            ls
     end.

Inductive plus_or_minus := PLUS | MINUS.
Inductive mul_or_div := MUL | DIV.

Definition parse_plus_or_minus := parse_ch [("+", PLUS); ("-", MINUS)]%char.
Definition parse_mul_or_div := parse_ch [("*", MUL); ("/", DIV)]%char.
Definition parse_open := parse_ch [("(", tt)]%char.
Definition parse_close := parse_ch [(")", tt)]%char.
Definition parse_pow := parse_ch [("^", tt)]%char.

Delimit Scope parse_scope with parse.

Definition maybe_parse {A} (parse : string -> option (A * string))
           (s : string)
  : option (option A * string)
  := Some match parse s with
          | Some (a, rest) => (Some a, rest)
          | None => (None, s)
          end.
Global Arguments maybe_parse {A%type} parse%parse s%string.

Definition bind_parse {A B} (parse_A : string -> option (A * string))
           (parse_B : A -> string -> option (B * string))
           (s : string)
  : option (B * string)
  := (a <- parse_A s;
        let '(a, s) := a in
        parse_B a s).
Global Arguments bind_parse {A B}%type (parse_A parse_B)%parse s%string.

Definition ret {A} (a : A) (s : string) : option (A * string)
  := Some (a, s).

Definition orelse {A}
           (parse parse' : string -> option (A * string))
           (s : string)
  : option (A * string)
  := match parse s with
     | Some v => Some v
     | None => parse' s
     end.
Global Arguments orelse {A%type} (parse parse')%parse s%string.

Local Open Scope parse_scope.
Notation "a <- parse_A ; parse_B" := (bind_parse parse_A%parse (fun a => parse_B%parse)) : parse_scope.
Infix "||" := orelse : parse_scope.

Fixpoint parse_Z (s : string) : option (Z * string)
  := match s with
     | String ch rest
       => if ascii_beq ch "+"
          then parse_Z rest
          else if ascii_beq ch "-"
               then match parse_Z rest with
                    | Some (z, s) => Some (-z, s)%Z
                    | None => None
                    end
               else match parse_N s with
                    | Some (v, s) => Some (Z.of_N v, s)
                    | None => None
                    end
     | EmptyString => None
     end.

Fixpoint parse_op_fueled
         {A B}
         (ops : list (ascii * (A -> B -> A)))
         (prev_parse : string -> option (B * string))
         (fuel : nat) (acc : A) : string -> option (A * string)
  := match fuel with
     | O => ret acc
     | S fuel'
       => (op <- parse_ch ops;
             z <- prev_parse;
             let acc := op acc z in
             parse_op_fueled ops prev_parse fuel' acc)
          || ret acc
     end.

Definition parse_op_from_acc
           {A B}
           (ops : list (ascii * (A -> B -> A)))
           (prev_parse : string -> option (B * string))
           (acc : A) (s : string) : option (A * string)
  := parse_op_fueled ops prev_parse (String.length s) acc s.

Definition parse_op
           {A}
           (ops : list (ascii * (A -> A -> A)))
           (prev_parse : string -> option (A * string))
  : string -> option (A * string)
  := acc <- prev_parse;
       parse_op_from_acc ops prev_parse acc.

Fixpoint parse_parens_fueled
         {A}
         (inj : Z -> A)
         (prev_parse : string -> option (A * string))
         (fuel : nat) : string -> option (A * string)
  := match fuel with
     | O => fun _ => None
     | S fuel'
       => ((_ <- parse_open;
              z <- prev_parse;
              _ <- parse_close;
              ret z)
           || (z <- parse_Z; ret (inj z)))
     end.

Inductive Zexpr := Zv (_ : Z) | Zopp (a : Zexpr) | Zadd (a b : Zexpr) | Zsub (a b : Zexpr) | Zmul (a b : Zexpr) | Zdiv (a b : Zexpr) | Zpow (b e : Zexpr).
Coercion Zv : Z >-> Zexpr.
Delimit Scope Zexpr_scope with Zexpr.
Bind Scope Zexpr_scope with Zexpr.
Infix "^" := Zpow : Zexpr_scope.
Infix "*" := Zmul : Zexpr_scope.
Infix "+" := Zadd : Zexpr_scope.
Infix "/" := Zdiv : Zexpr_scope.
Infix "-" := Zsub : Zexpr_scope.
Notation "- x" := (Zopp x) : Zexpr_scope.

Fixpoint eval_Zexpr (v : Zexpr) : Z
  := match v with
     | Zv x => x
     | Zopp a => Z.opp (eval_Zexpr a)
     | Zadd a b => Z.add (eval_Zexpr a) (eval_Zexpr b)
     | Zsub a b => Z.sub (eval_Zexpr a) (eval_Zexpr b)
     | Zmul a b => Z.mul (eval_Zexpr a) (eval_Zexpr b)
     | Zdiv a b => Z.div (eval_Zexpr a) (eval_Zexpr b)
     | Zpow b e => Z.pow (eval_Zexpr b) (eval_Zexpr e)
     end.

Section gen.
  Context {A}
          (Zadd : A -> A -> A)
          (Zsub : A -> A -> A)
          (Zmul : A -> A -> A)
          (Zdiv : A -> A -> A)
          (Zpow : A -> A -> A)
          (inj : Z -> A).
  Section step.
    Context (parseZ : string -> option (A * string)).

    Definition parseZ_gen_parens (s : string) : option (A * string)
      := parse_parens_fueled inj parseZ (String.length s) s.
    Definition parseZ_gen_exp : string -> option (A * string)
      := parse_op [("^", Zpow)]%char parseZ_gen_parens.
    Definition parseZ_gen_mul_div : string -> option (A * string)
      := parse_op [("*", Zmul); ("/", Zdiv)]%char parseZ_gen_exp.
    Definition parseZ_gen_add_sub : string -> option (A * string)
      := parse_op [("+", Zadd); ("-", Zsub)]%char parseZ_gen_mul_div.
  End step.

  Fixpoint parseZ_gen_arith_fueled (fuel : nat) : string -> option (A * string)
    := match fuel with
       | O => parseZ_gen_add_sub (z <- parse_Z; ret (inj z))
       | S fuel' => parseZ_gen_add_sub (parseZ_gen_arith_fueled fuel')
       end.

  Definition parseZ_gen_arith_prefix (s : string) : option (A * string)
    := parseZ_gen_arith_fueled (String.length s) s.
End gen.

Definition parseZ_arith_prefix : string -> option (Z * string)
  := parseZ_gen_arith_prefix Z.add Z.sub Z.mul Z.div Z.pow id.

Definition parseZexpr_arith_prefix : string -> option (Zexpr * string)
  := parseZ_gen_arith_prefix Zadd Zsub Zmul Zdiv Zpow id.

Fixpoint remove_spaces (s : string) : string
  := match s with
     | EmptyString => EmptyString
     | String ch s
       => let s' := remove_spaces s in
          if ascii_beq ch " " then s' else String ch s'
     end.

Definition parseZ_arith (s : string) : option Z
  := match parseZ_arith_prefix (remove_spaces s) with
     | Some (z, EmptyString) => Some z
     | _ => None
     end.

Definition parseZexpr_arith (s : string) : option Zexpr
  := match parseZexpr_arith_prefix (remove_spaces s) with
     | Some (z, EmptyString) => Some z
     | _ => None
     end.
