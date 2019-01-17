Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.Strings.Decimal.
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

Fixpoint split_before_first (f : ascii -> bool) (s : string) : string * string
  := match s with
     | EmptyString => (EmptyString, EmptyString)
     | String ch rest
       => if f ch
          then (EmptyString, s)
          else let '(s1, s2) := split_before_first f rest in
               (String ch s1, s2)
     end.

Definition parse_N (s : string) : option (N * string)
  := let '(n, rest) := split_before_first (fun ch => negb (is_num ch)) s in
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

Fixpoint parseZ_op_fueled
         (ops : list (ascii * (Z -> Z -> Z)))
         (prev_parse : string -> option (Z * string))
         (fuel : nat) (acc : Z) : string -> option (Z * string)
  := match fuel with
     | O => ret acc
     | S fuel'
       => (op <- parse_ch ops;
             z <- prev_parse;
             let acc := op acc z in
             parseZ_op_fueled ops prev_parse fuel' acc)
          || ret acc
     end.

Definition parseZ_op_from_acc
         (ops : list (ascii * (Z -> Z -> Z)))
         (prev_parse : string -> option (Z * string))
         (acc : Z) (s : string) : option (Z * string)
  := parseZ_op_fueled ops prev_parse (String.length s) acc s.

Definition parseZ_op
         (ops : list (ascii * (Z -> Z -> Z)))
         (prev_parse : string -> option (Z * string))
  : string -> option (Z * string)
  := acc <- prev_parse;
       parseZ_op_from_acc ops prev_parse acc.

Fixpoint parseZ_parens_fueled
         (prev_parse : string -> option (Z * string))
         (fuel : nat) : string -> option (Z * string)
  := match fuel with
     | O => fun _ => None
     | S fuel'
       => ((_ <- parse_open;
              z <- prev_parse;
              _ <- parse_close;
              ret z)
           || parse_Z)
     end.

Section step.
  Context (parseZ : string -> option (Z * string)).

  Definition parseZ_parens (s : string) : option (Z * string)
    := parseZ_parens_fueled parseZ (String.length s) s.
  Definition parseZ_exp : string -> option (Z * string)
    := parseZ_op [("^", Z.pow)]%char parseZ_parens.
  Definition parseZ_mul_div : string -> option (Z * string)
    := parseZ_op [("*", Z.mul); ("/", Z.div)]%char parseZ_exp.
  Definition parseZ_add_sub : string -> option (Z * string)
    := parseZ_op [("+", Z.add); ("-", Z.sub)]%char parseZ_mul_div.
End step.

Fixpoint parseZ_arith_fueled (fuel : nat) : string -> option (Z * string)
  := match fuel with
     | O => parseZ_add_sub parse_Z
     | S fuel' => parseZ_add_sub (parseZ_arith_fueled fuel')
     end.

Definition parseZ_arith_prefix (s : string) : option (Z * string)
  := parseZ_arith_fueled (String.length s) s.

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
