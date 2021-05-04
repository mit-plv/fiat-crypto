Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.HexString.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Stringification.IR.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.


Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Export Language.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.ZRange.Compilers.
  Export Stringification.Language.Compilers.
  Import invert_expr.
  Import Compilers.API.

  Module ToString.
    Import Stringification.Language.Compilers.ToString.
    Import Stringification.Language.Compilers.ToString.ZRange.
    Import Compilers.ToString.IR.
    Local Open Scope string_scope.
    Local Open Scope Z_scope.

    Local Notation tZ := (base.type.type_base base.type.Z).

    Module C.
      Definition comment_block := List.map (fun line => "/* " ++ line ++ " */")%string.

      Definition FIAT_INLINE (prefix : string) := (String.to_upper prefix ++ "FIAT_INLINE")%string.

      Module String.
        Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
        Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).

        Module int.
          Module type.
            Definition to_string_opt_typedef {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (prefix : string) (t : int.type) (typedef : option string) : string
              := int.to_string_gen_opt_typedef stdint_bitwidths "uint" "int" "_t" "" false(*type declarations not static*) false(*typedef declarations are not static*) prefix t typedef.
            Definition to_string {language_naming_conventions : language_naming_conventions_opt} (prefix : string) (t : int.type) : string
              := to_string_opt_typedef (skip_typedefs:=true) prefix t None.
            Definition to_literal_macro_string (t : int.type) : option string
              := if Z.ltb (int.bitwidth_of t) 8
                 then None
                 else Some ((if int.is_unsigned t then "U" else "")
                              ++ "INT"
                              ++ Decimal.Z.to_string (int.bitwidth_of t)
                              ++ "_C")%string.
          End type.
        End int.

        Module type.
          Module primitive.
            Definition to_string_opt_typedef {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (prefix : string) (t : type.primitive) (r : option int.type) (typedef : option string) : string
              := match r with
                 | Some int_t => int.type.to_string_opt_typedef prefix int_t typedef
                 | None => "ℤ"
                 end ++ match t with
                        | type.Zptr => "*"
                        | type.Z => ""
                        end.
            Definition to_string {language_naming_conventions : language_naming_conventions_opt} (prefix : string) (t : type.primitive) (r : option int.type) : string
              := to_string_opt_typedef (skip_typedefs:=true) prefix t r None.
          End primitive.
        End type.

        Definition value_barrier_name {language_naming_conventions : language_naming_conventions_opt} (static : bool) (prefix : string) (ty : int.type) : string
          := format_special_function_name_ty static prefix "value_barrier" ty.
        Definition value_barrier_func {language_naming_conventions : language_naming_conventions_opt} (static : bool) (prefix : string) (ty : int.type) : list string
          := [""
              ; "#if !defined(" ++ String.to_upper prefix ++ "NO_ASM) && (defined(__GNUC__) || defined(__clang__))"
              ; (if static then "static " else "") ++ "__inline__ " ++ int.type.to_string prefix ty ++ " " ++ value_barrier_name static prefix ty ++ "(" ++ int.type.to_string prefix ty ++ " a) {"
              ; "  __asm__("""" : ""+r""(a) : /* no inputs */);"
              ; "  return a;"
              ; "}"
              ; "#else"
              ; "#  define " ++ value_barrier_name static prefix ty ++ "(x) (x)"
              ; "#endif"].

        Definition make_typedef
                   {language_naming_conventions : language_naming_conventions_opt}
                   {documentation_options : documentation_options_opt}
                   (prefix : string)
                   (typedef : typedef_info)
          : list string
          := let '(name, (ty, array_len), description) := name_and_type_and_describe_typedef prefix false(*type declarations not static*) typedef in
             ((comment_block description)
                ++ match array_len with
                   | None (* just an integer *)
                     => ["typedef " ++ String.type.primitive.to_string prefix type.Z ty ++ " " ++ name ++ ";"]
                   | Some None (* unknown array length *)
                     => ["typedef " ++ String.type.primitive.to_string prefix type.Zptr ty ++ " " ++ name ++ ";"]
                   | Some (Some len)
                     => ["typedef " ++ String.type.primitive.to_string prefix type.Z ty ++ " " ++ name ++ "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "];"]
                   end%string)%list.

        Definition header
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {package_namev : package_name_opt}
             {class_namev : class_name_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z) (internal_static : bool) (static : bool) (prefix : string) (infos : ident_infos)
             (typedef_map : list typedef_info)
        : list string
          := let bitwidths_used := bitwidths_used infos in
             let value_barrier_bitwidths := value_barrier_bitwidths infos in
             let FIAT_EXTENSION := (String.to_upper prefix ++ "FIAT_EXTENSION")%string in
             (["";
              "#include <stdint.h>"]
                ++ (if IntSet.mem _Bool bitwidths_used || IntSet.mem (int.signed_counterpart_of _Bool) bitwidths_used
                    then ["typedef unsigned char " ++ int.type.to_string prefix _Bool ++ ";";
                            "typedef signed char " ++ int.type.to_string prefix (int.signed_counterpart_of _Bool) ++ ";"]%string
                    else [])
                ++ (let gnuc_defines
                        := (if IntSet.mem uint128 bitwidths_used || IntSet.mem int128 bitwidths_used
                            then [(FIAT_EXTENSION, "__extension__")]
                            else [])
                             ++ [(FIAT_INLINE prefix, "__inline__")]
                    in
                    ["#if defined(__GNUC__) || defined(__clang__)"]
                      ++ List.map (fun '(MACRO, primitive) => "#  define " ++ MACRO ++ " " ++ primitive)%string gnuc_defines
                      ++ ["#else"]
                      ++ List.map (fun '(MACRO, primitive) => "#  define " ++ MACRO)%string gnuc_defines
                      ++ ["#endif"])
                ++ (if IntSet.mem uint128 bitwidths_used || IntSet.mem int128 bitwidths_used
                    then ["";
                         FIAT_EXTENSION ++ " typedef signed __int128 " ++ int.type.to_string prefix int128 ++ ";";
                         FIAT_EXTENSION ++ " typedef unsigned __int128 " ++ int.type.to_string prefix uint128 ++ ";"]%string
                    else [])
                ++ (if skip_typedefs
                    then []
                    else List.flat_map
                           (fun td_name =>
                              match List.find (fun '(name, _, _, _) => (td_name =? name)%string) typedef_map with
                              | Some td_info => [""] ++ make_typedef prefix td_info
                              | None => ["#error ""Could not find typedef info for '" ++ td_name ++ "'"";"]%string
                              end%list)
                           (typedefs_used infos))
                ++ [""
                    ; "#if (-1 & 3) != 3"
                    ; "#error ""This code only works on a two's complement system"""
                    ; "#endif"]
                ++ (List.flat_map
                      (value_barrier_func internal_static prefix)
                      (IntSet.elements value_barrier_bitwidths))
                ++ [""])%list.
      End String.

      Module primitive.
        Definition to_string (prefix : string) (t : type.primitive) (v : BinInt.Z) : string
          := match t, String.int.type.to_literal_macro_string (int.of_zrange_relaxed r[v ~> v]) with
             | type.Z, Some macro
               => macro ++ "(" ++ HexString.of_Z v ++ ")"
             | type.Z, None => HexString.of_Z v
             | type.Zptr, _ => "#error ""literal address " ++ HexString.of_Z v ++ """;"
             end.
      End primitive.

      (** Quoting https://en.cppreference.com/w/c/language/operator_precedence:

<<
Precedence |   Operator   |              Description                | Associativity
-----------------------------------------------------------------------------------
1          | ++ --        | Suffix/postfix increment and decrement  | Left-to-right
           | ()           | Function call                           |
           | []           | Array subscripting                      |
           | .            | Structure and union member access       |
           | ->           | Structure and union member access       |
           |              |    through pointer                      |
           | (type){list} | Compound literal(C99)                   |
-----------|--------------|-----------------------------------------|--------------
2          | ++ --        | Prefix increment and decrement[note 1]  | Right-to-left
           | + -          | Unary plus and minus                    |
           | ! ~          | Logical NOT and bitwise NOT             |
           | (type)       | Cast                                    |
           | *            | Indirection (dereference)               |
           | &            | Address-of                              |
           | sizeof       | Size-of[note 2]                         |
           | _Alignof     | Alignment requirement(C11)              |
-----------|--------------|-----------------------------------------|--------------
3          | * / %        | Multiplication, division, and remainder | Left-to-right
-----------|--------------|-----------------------------------------|
4          | + -          | Addition and subtraction                |
-----------|--------------|-----------------------------------------|
5          | << >>        | Bitwise left shift and right shift      |
-----------|--------------|-----------------------------------------|
6          | < <=         | For relational operators < and ≤        |
           |              |   respectively                          |
           | > >=         | For relational operators > and ≥        |
           |              |   respectively                          |
-----------|--------------|-----------------------------------------|
7          |== !=         | For relational = and ≠ respectively     |
-----------|--------------|-----------------------------------------|
8          | &            | Bitwise AND                             |
-----------|--------------|-----------------------------------------|
9          | ^            | Bitwise XOR (exclusive or)              |
-----------|--------------|-----------------------------------------|
10         | |            | Bitwise OR (inclusive or)               |
-----------|--------------|-----------------------------------------|
11         | &&           | Logical AND                             |
-----------|--------------|-----------------------------------------|
12         | ||           | Logical OR                              |
-----------|--------------|-----------------------------------------|--------------
13         | ?:           | Ternary conditional[note 3]             | Right-to-left
-----------|--------------|-----------------------------------------|
14[note 4] | =            | Simple assignment                       |
           | += -=        | Assignment by sum and difference        |
           | *= /= %=     | Assignment by product, quotient, and    |
           |              |   remainder                             |
           | <<= >>=      | Assignment by bitwise left shift and    |
           |              |   right shift                           |
           | &= ^= |=     | Assignment by bitwise AND, XOR, and OR  |
-----------|--------------|-----------------------------------------|--------------
15         | ,            | Comma                                   | Left-to-right
>>
       *)
      (**

      1. The operand of prefix ++ and -- can't be a type cast. This
         rule grammatically forbids some expressions that would be
         semantically invalid anyway. Some compilers ignore this rule
         and detect the invalidity semantically.

      2. The operand of sizeof can't be a type cast: the expression
         sizeof (int) * p is unambiguously interpreted as
         (sizeof(int)) * p, but not sizeof((int)*p).

      3. The expression in the middle of the conditional operator
         (between ? and :) is parsed as if parenthesized: its
         precedence relative to ?: is ignored.

      4. Assignment operators' left operands must be unary (level-2
         non-cast) expressions. This rule grammatically forbids some
         expressions that would be semantically invalid anyway. Many
         compilers ignore this rule and detect the invalidity
         semantically. For example, e = a < d ? a++ : a = d is an
         expression that cannot be parsed because of this
         rule. However, many compilers ignore this rule and parse it
         as e = ( ((a < d) ?  (a++) : a) = d ), and then give an error
         because it is semantically invalid.

      When parsing an expression, an operator which is listed on some
      row will be bound tighter (as if by parentheses) to its
      arguments than any operator that is listed on a row further
      below it. For example, the expression *p++ is parsed as *(p++),
      and not as ( *p )++.

      Operators that are in the same cell (there may be several rows
      of operators listed in a cell) are evaluated with the same
      precedence, in the given direction. For example, the expression
      a=b=c is parsed as a=(b=c), and not as (a=b)=c because of
      right-to-left associativity.  *)

      (** Since unary operators are ambiguous (is --a -(-a) or --a?), we bind the arguments of -, --, +, ++ at one level lower so that they are always parenthesized *)

      Definition C_postop_precedence_table : list (string * (Associativity * Level))
        := [("++", (LeftAssoc, Level.level 1)); ("--", (LeftAssoc, Level.level 1)) (* Suffix/postfix increment and decrement *)
            ; ("()", (LeftAssoc, Level.level 1)) (* Function call *)
            ; ("[]", (LeftAssoc, Level.level 1)) (* Array subscripting *)
            ; ("." , (LeftAssoc, Level.level 1)) (* Structure and union member access *)
            ; ("->", (LeftAssoc, Level.level 1)) (* Structure and union member access through pointer *)
            ; ("(type){list}", (LeftAssoc, Level.level 1)) (* Compound literal(C99) *)
           ].
      Definition C_preop_precedence_table : list (string * (Associativity * Level))
        := [("++", (ExplicitAssoc 1 1, Level.level 2)); ("--", (ExplicitAssoc 1 1, Level.level 2)) (* Prefix increment and decrement *)
            ; ("+", (ExplicitAssoc 1 1, Level.level 2)); ("-", (ExplicitAssoc 1 1, Level.level 2)) (* Unary plus and minus *)
            ; ("!", (RightAssoc, Level.level 2)); ("~", (RightAssoc, Level.level 2)) (* Logical NOT and bitwise NOT *)
            ; ("(type)", (RightAssoc, Level.level 2)) (* Cast *)
            ; ("*", (RightAssoc, Level.level 2)) (* Indirection (dereference) *)
            ; ("&", (RightAssoc, Level.level 2)) (* Address-of *)
            ; ("sizeof", (RightAssoc, Level.level 2)) (* Size-of (* args at level below (type) cast because argument cannot be a type cast *) *)
            ; ("_Alignof", (RightAssoc, Level.level 2))
           ].
      Definition C_binop_precedence_table : list (string * (Associativity * Level))
        := [("*", (LeftAssoc, Level.level 3)); ("/", (LeftAssoc, Level.level 3)); ("%", (LeftAssoc, Level.level 3)) (* Multiplication, division, and remainder *)
            ; ("+", (LeftAssoc, Level.level 4)); ("-", (LeftAssoc, Level.level 4)) (* Addition and subtraction *)
            ; ("<<", (LeftAssoc, Level.level 5)); (">>", (LeftAssoc, Level.level 5)) (* Bitwise left shift and right shift *)
            ; ("<", (LeftAssoc, Level.level 6)); ("<=", (LeftAssoc, Level.level 6)) (* For relational operators < and ≤ respectively *)
            ; (">", (LeftAssoc, Level.level 6)); (">=", (LeftAssoc, Level.level 6)) (* For relational operators > and ≥ respectively *)
            ; ("==", (LeftAssoc, Level.level 7)); ("!=", (LeftAssoc, Level.level 7)) (* For relational = and ≠ respectively *)
            ; ("&", (LeftAssoc, Level.level 8)) (* Bitwise AND *)
            ; ("^", (LeftAssoc, Level.level 9)) (* Bitwise XOR (exclusive or) *)
            ; ("|", (LeftAssoc, Level.level 10)) (* Bitwise OR (inclusive or) *)
            ; ("&&", (LeftAssoc, Level.level 10)) (* Logical AND *)
            ; ("||", (LeftAssoc, Level.level 10)) (* Logical OR *)
            ; ("?:", (RightAssoc, Level.level 10)) (* Ternary conditional[note 3] *)
            ; ("=", (ExplicitAssoc 2 14, Level.level 10)) (* Simple assignment; Assignment operators' left operands must be unary (level-2 non-cast) expressions. *)
            ; ("+=", (ExplicitAssoc 2 14, Level.level 11)); ("-=", (ExplicitAssoc 2 14, Level.level 11)) (* Assignment by sum and difference *)
            ; ("*=", (ExplicitAssoc 2 14, Level.level 12)); ("/=", (ExplicitAssoc 2 14, Level.level 12)); ("%=", (ExplicitAssoc 2 14, Level.level 12)) (* Assignment by product, quotient, and remainder *)
            ; ("<<=", (ExplicitAssoc 2 14, Level.level 13)); (">>=", (ExplicitAssoc 2 14, Level.level 13)) (* Assignment by bitwise left shift and right shift *)
            ; ("&=", (ExplicitAssoc 2 14, Level.level 14)); ("^=", (ExplicitAssoc 2 14, Level.level 14)); ("|=", (ExplicitAssoc 2 14, Level.level 14)) (* Assignment by bitwise AND, XOR, and OR *)
            ; (", ", (LeftAssoc, Level.level 10)) (* Comma *)
           ].

      Definition ident_to_op_string {a b} (idc : ident a b) : string
        := match idc with
           | List_nth _ => "[]"
           | Addr => "&"
           | Dereference => "*"
           | Z_shiftr _ => ">>"
           | Z_shiftl _ => "<<"
           | Z_lnot _ => "~"
           | Z_bneg => "!"
           | Z_land => "&"
           | Z_lor => "|"
           | Z_lxor => "^"
           | Z_add => "+"
           | Z_mul => "*"
           | Z_sub => "-"
           | Z_static_cast _ => "(type)"
           | Z_mul_split _
           | Z_add_with_get_carry _
           | Z_sub_with_get_borrow _
           | Z_zselect _
           | Z_add_modulo
           | Z_value_barrier _
           | literal _
             => ""
           end.

      (* _s for string rather than ident *)
      Local Notation show_lvl_binop_s_no_space binop := (PHOAS.ident.lookup_show_lvl_binop (with_space:=false) C_binop_precedence_table binop).
      Local Notation show_lvl_binop_no_space idc := (show_lvl_binop_s_no_space (ident_to_op_string idc)).
      Local Notation show_lvl_binop_s binop := (PHOAS.ident.lookup_show_lvl_binop (with_space:=true) C_binop_precedence_table binop).
      Local Notation show_lvl_binop idc := (show_lvl_binop_s (ident_to_op_string idc)).
      Local Notation show_lvl_preop idc := (PHOAS.ident.lookup_show_lvl_preop C_preop_precedence_table (ident_to_op_string idc)).
      Local Notation show_lvl_postop idc := (PHOAS.ident.lookup_show_lvl_postop C_postop_precedence_table (ident_to_op_string idc)).
      Local Notation lookup_preop_assoc idc := (PHOAS.ident.lookup_assoc C_preop_precedence_table (ident_to_op_string idc)).
      Local Notation lookup_postop_assoc idc := (PHOAS.ident.lookup_assoc C_postop_precedence_table (ident_to_op_string idc)).
      Local Notation lookup_binop_assoc_s binop := (PHOAS.ident.lookup_assoc C_binop_precedence_table binop).
      Local Notation lookup_binop_assoc idc := (lookup_binop_assoc_s (ident_to_op_string idc)).
      Local Notation lookup_preop_lvl idc := (PHOAS.ident.lookup_lvl C_preop_precedence_table (ident_to_op_string idc)).
      Local Notation lookup_postop_lvl idc := (PHOAS.ident.lookup_lvl C_postop_precedence_table (ident_to_op_string idc)).
      Local Notation lookup_binop_lvl_s binop := (PHOAS.ident.lookup_lvl C_binop_precedence_table binop).
      Local Notation lookup_binop_lvl idc := (lookup_binop_lvl_s (ident_to_op_string idc)).
      Local Notation fn_call_lvl := (PHOAS.ident.lookup_lvl C_postop_precedence_table "()").
      Local Notation fn_call f e := (lvl_wrap_parens fn_call_lvl (f ++ "(" ++ show_lvl e ∞ ++ ")")).
      (** Use a [Definition] wrapped around a [fix] so that we get the
          type of the definition to be [ShowLevel] while still
          otherwise having the exact behavior as if we had used
          [Fixpoint] *)
      Definition arith_to_string
        : forall {language_naming_conventions : language_naming_conventions_opt} (internal_static : bool)
                 (prefix : string) {t}, ShowLevel (arith_expr t)
        := fix arith_to_string {language_naming_conventions : language_naming_conventions_opt} (internal_static : bool)
               (prefix : string) {t} (e : arith_expr t) {struct e} : Level -> string
             := let special_name_ty name ty := format_special_function_name_ty internal_static prefix name ty in
                let special_name name bw := format_special_function_name internal_static prefix name false(*unsigned*) bw in
                let _ (* for tc resolution *) : forall {t}, ShowLevel (arith_expr t) := fun t => arith_to_string internal_static prefix (t:=t) in
                match e with
                | (literal v @@@ _) => neg_wrap_parens (primitive.to_string prefix type.Z v)
                | ((List_nth n as idc) @@@ Var _ v)
                  => show_lvl_postop_assoc (lookup_postop_assoc idc) (lookup_postop_lvl idc) (fun 'tt => v) ("[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "]")
                | ((Addr as idc) @@@ Var _ v)
                  => show_lvl_preop idc (neg_wrap_parens v)
                | ((Dereference as idc) @@@ e)
                | ((Z_lnot _ as idc) @@@ e)
                | ((Z_bneg as idc) @@@ e)
                  => show_lvl_preop idc (show_lvl e)
                | ((Z_shiftr offset as idc) @@@ e)
                | ((Z_shiftl offset as idc) @@@ e)
                  => show_lvl_binop idc (show_lvl e) (neg_wrap_parens (Decimal.Z.to_string offset))
                | ((Z_land as idc) @@@ (e1, e2))
                | ((Z_lor as idc) @@@ (e1, e2))
                | ((Z_lxor as idc) @@@ (e1, e2))
                | ((Z_add as idc) @@@ (e1, e2))
                | ((Z_mul as idc) @@@ (e1, e2))
                | ((Z_sub as idc) @@@ (e1, e2))
                  => show_lvl_binop idc (show_lvl e1) (show_lvl e2)
                | (Z_value_barrier ty @@@ args)
                  => fn_call (String.value_barrier_name internal_static prefix ty) args
                | (Z_mul_split lg2s @@@ args)
                  => fn_call (special_name "mulx" lg2s) args
                | (Z_add_with_get_carry lg2s @@@ args)
                  => fn_call (special_name "addcarryx" lg2s) args
                | (Z_sub_with_get_borrow lg2s @@@ args)
                  => fn_call (special_name "subborrowx" lg2s) args
                | (Z_zselect ty @@@ args)
                  => fn_call (special_name_ty "cmovznz" ty) args
                | (Z_add_modulo @@@ (x1, x2, x3)) => neg_wrap_parens "#error addmodulo;"
                | ((Z_static_cast int_t as idc) @@@ e)
                  => show_lvl_preop_assoc
                       (lookup_preop_assoc idc) (lookup_preop_lvl idc)
                       ("(" ++ String.type.primitive.to_string prefix type.Z (Some int_t) ++ ")")
                       (show_lvl e)
                | Var _ v => neg_wrap_parens v
                | Pair A B a b
                  => Show.show_lvl_binop
                       FullyAssoc (* function call arguments can be passed in any order *)
                       (Level.prev (lookup_binop_lvl_s ", ")) (* function call [,] MUST bind more tightly than [,] as a binary operator in C, otherwise if we ever support [,] as a binary operator, we'll end up printing [f((_, x), (_, y))] as [f(_, x, _, y)] *)
                       a ", " b
                | (List_nth _ @@@ _)
                | (Addr @@@ _)
                | (Z_add @@@ _)
                | (Z_mul @@@ _)
                | (Z_sub @@@ _)
                | (Z_land @@@ _)
                | (Z_lor @@@ _)
                | (Z_lxor @@@ _)
                | (Z_add_modulo @@@ _)
                  => neg_wrap_parens "#error bad_arg;"
                | TT
                  => neg_wrap_parens "#error tt;"
                end%core%Cexpr.

      Definition stmt_to_string
            {language_naming_conventions : language_naming_conventions_opt} (internal_static : bool)
            (prefix : string)
        : Show stmt
        := fun e
           => match e with
              | Call val
                => arith_to_string internal_static prefix val ∞ ++ ";"
              | Assign true t sz name val
                => String.type.primitive.to_string prefix t sz ++ " " ++ name ++ " = " ++ arith_to_string internal_static prefix val (lookup_binop_lvl_s "=") ++ ";"
              | Assign false _ sz name val
                => name ++ " = " ++ arith_to_string internal_static prefix val (lookup_binop_lvl_s "=") ++ ";"
              | AssignZPtr name sz val
                => "*" ++ name ++ " = " ++ arith_to_string internal_static prefix val (lookup_binop_lvl_s "=") ++ ";"
              | DeclareVar t sz name
                => String.type.primitive.to_string prefix t sz ++ " " ++ name ++ ";"
              | Comment lines _
                => String.concat String.NewLine (comment_block (ToString.preprocess_comment_block lines))
              | AssignNth name n val
                => name ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "] = " ++ arith_to_string internal_static prefix val (lookup_binop_lvl_s "=") ++ ";"
              end.
      Definition to_strings
                 {language_naming_conventions : language_naming_conventions_opt} (internal_static : bool)
                 (prefix : string)
                 (e : expr)
        : list string
        := List.map (stmt_to_string internal_static prefix) e.

      Import OfPHOAS.

      Fixpoint to_base_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (prefix : string) {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | tZ
             => fun '(n, is_ptr, r, typedef)
                => [String.type.primitive.to_string_opt_typedef prefix type.Z r typedef ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (to_base_arg_list prefix va ++ to_base_arg_list prefix vb)%list
           | base.type.list tZ
             => fun '(n, r, len, typedef)
                => ["const "
                      ++ match (if skip_typedefs then None else typedef) with
                         | Some typedef => format_typedef_name prefix false(*type declarations not static*) typedef ++ " " ++ n
                         | None => String.type.primitive.to_string prefix type.Z r ++ " " ++ n ++ "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]"
                         end]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.option _ => fun _ => ["#error option;"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.type_base t => fun _ => ["#error " ++ show t ++ ";"]%string
           end.

      Definition to_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (prefix : string) {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base t => to_base_arg_list prefix
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Fixpoint to_arg_list_for_each_lhs_of_arrow {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> _ with
           | type.base t => fun _ => nil
           | type.arrow s d
             => fun '(x, xs)
                => to_arg_list prefix x ++ to_arg_list_for_each_lhs_of_arrow prefix xs
           end%list.

      Fixpoint to_base_retarg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} prefix {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | tZ
             => fun '(n, is_ptr, r, typedef)
                => [match typedef with
                    | Some typedef => format_typedef_name prefix false(*type declarations not static*) typedef ++ "*"
                    | None => String.type.primitive.to_string prefix type.Zptr r
                    end
                      ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (to_base_retarg_list prefix va ++ to_base_retarg_list prefix vb)%list
           | base.type.list tZ
             => fun '(n, r, len, typedef)
                => [match (if skip_typedefs then None else typedef) with
                    | Some typedef => format_typedef_name prefix false(*type declarations not static*) typedef ++ " " ++ n
                    | None => String.type.primitive.to_string prefix type.Z r ++ " " ++ n ++ "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]"
                    end]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.option _ => fun _ => ["#error option;"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.type_base t => fun _ => ["#error " ++ show t ++ ";"]%string
           end.

      Definition to_retarg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (prefix : string) {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base _ => to_base_retarg_list prefix
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

      (** Quoting
          http://en.cppreference.com/w/c/language/conversion:

          ** Integer promotions

          Integer promotion is the implicit conversion of a value of
          any integer type with rank less or equal to rank of int or
          of a bit field of type _Bool, int, signed int, unsigned
          int, to the value of type int or unsigned int

          If int can represent the entire range of values of the
          original type (or the range of values of the original bit
          field), the value is converted to type int. Otherwise the
          value is converted to unsigned int. *)
      (** We assume a 32-bit [int] type *)
      Definition integer_promote_type (t : int.type) : int.type
        := if int.is_tighter_than t int32
           then int32
           else t.


      (** Quoting
          http://en.cppreference.com/w/c/language/conversion:

          rank above is a property of every integer type and is
          defined as follows:

          1) the ranks of all signed integer types are different and
             increase with their precision: rank of signed char <
             rank of short < rank of int < rank of long int < rank
             of long long int

          2) the ranks of all signed integer types equal the ranks
             of the corresponding unsigned integer types

          3) the rank of any standard integer type is greater than
             the rank of any extended integer type of the same size
             (that is, rank of __int64 < rank of long long int, but
             rank of long long < rank of __int128 due to the rule
             (1))

          4) rank of char equals rank of signed char and rank of
             unsigned char

          5) the rank of _Bool is less than the rank of any other
             standard integer type

          6) the rank of any enumerated type equals the rank of its
             compatible integer type

          7) ranking is transitive: if rank of T1 < rank of T2 and
             rank of T2 < rank of T3 then rank of T1 < rank of T3

          8) any aspects of relative ranking of extended integer
             types not covered above are implementation defined *)
         (** We define the rank to be the bitwidth, which satisfies
             (1), (2), (4), (5), and (7).  Points (3) and (6) do not
             apply. *)
      Definition rank (r : int.type) : BinInt.Z := int.bitwidth_of r.
      Definition IMPOSSIBLE {T} (v : T) : T. exact v. Qed.
      (** Quoting
          http://en.cppreference.com/w/c/language/conversion: *)
      Definition C_common_type (t1 t2 : int.type) : int.type
        (** First of all, both operands undergo integer promotions
            (see below). Then *)
        := let t1 := integer_promote_type t1 in
           let t2 := integer_promote_type t2 in
           (** - If the types after promotion are the same, that
               type is the common type *)
           if int.type_beq t1 t2 then
             t1
           (** - Otherwise, if both operands after promotion have
                 the same signedness (both signed or both unsigned),
                 the operand with the lesser conversion rank (see
                 below) is implicitly converted to the type of the
                 operand with the greater conversion rank *)
           else if bool_beq (int.is_signed t1) (int.is_signed t2) then
                  (if rank t1 >=? rank t2 then t1 else t2)
           (** - Otherwise, the signedness is different: If the
                 operand with the unsigned type has conversion rank
                 greater or equal than the rank of the type of the
                 signed operand, then the operand with the signed
                 type is implicitly converted to the unsigned type
            *)
           else if int.is_unsigned t1 && (rank t1 >=? rank t2) then
             t1
           else if int.is_unsigned t2 && (rank t2 >=? rank t1) then
             t2
           (** - Otherwise, the signedness is different and the
                 signed operand's rank is greater than unsigned
                 operand's rank. In this case, if the signed type
                 can represent all values of the unsigned type, then
                 the operand with the unsigned type is implicitly
                 converted to the type of the signed operand. *)
           else if int.is_signed t1 && int.is_tighter_than t2 t1 then
             t1
           else if int.is_signed t2 && int.is_tighter_than t1 t2 then
             t2
           (** - Otherwise, both operands undergo implicit
                 conversion to the unsigned type counterpart of the
                 signed operand's type. *)
           (** N.B. This case ought to be impossible in our code,
               where [rank] is the bitwidth. *)
           else if int.is_signed t1 then
             int.unsigned_counterpart_of t1
           else
             int.unsigned_counterpart_of t2.

      (** Quoting https://en.cppreference.com/w/c/language/conversion: *)
      (** Usual arithmetic conversions

          The arguments of the following arithmetic operators undergo
          implicit conversions for the purpose of obtaining the common
          real type, which is the type in which the calculation is
          performed:

          - binary arithmetic *, /, %, +, -
          - relational operators <, >, <=, >=, ==, !=
          - binary bitwise arithmetic &, ^, |,
          - the conditional operator ?: *)
      Inductive binop_kind := use_common_type.
      Definition kind_of_binop (idc : Z_binop) : binop_kind
        := match idc with
           | Z_land
           | Z_lor
           | Z_lxor
           | Z_add
           | Z_mul
           | Z_sub
             => use_common_type
           end.

      Definition C_bin_op_natural_output
        : Z_binop -> int.type * int.type -> int.type
        := fun idc '(t1, t2)
           => match kind_of_binop idc with
              | use_common_type => C_common_type t1 t2
              end.

      Definition C_bin_op_casts
        : Z_binop -> option int.type -> int.type * int.type -> option int.type * (option int.type * option int.type)
        := fun idc desired_type '(t1, t2)
           => match kind_of_binop idc with
              | use_common_type
                => match desired_type with
                   | None => (None, (None, None))
                   | Some _
                     => let t1 := integer_promote_type t1 in
                        let t2 := integer_promote_type t2 in
                        let '(t1o, t2o)
                            := if int.is_tighter_than t2 t1
                               then (get_Zcast_up_if_needed desired_type (Some t1), None)
                               else (None, get_Zcast_up_if_needed desired_type (Some t2)) in
                        let ct := C_common_type (Option.value t1o t1) (Option.value t2o t2) in
                        (get_Zcast_down_if_needed desired_type (Some ct), (t1o, t2o))
                   end
              end.

      Definition C_un_op_casts
        : Z_unop -> option int.type -> int.type -> option int.type * option int.type
        := fun idc desired_type t
           => let t := integer_promote_type t in
              match idc with
              | Z_shiftr offset
                => (** N.B. We must cast the expression up to a large
                       enough type to fit 2^offset (importantly, not
                       just 2^offset-1), because C considers it to be
                       undefined behavior to shift >= width of the
                       type.  We should probably figure out how to not
                       generate these things in the first place...

                       N.B. We must preserve signedness of the value
                       being shifted, because shift does not commute
                       with mod. *)
                let t' := int.union_zrange r[0~>2^offset]%zrange t in
                ((** We cast the result down to the specified type, if needed *)
                  get_Zcast_down_if_needed desired_type (Some t'),
                  (** We cast the argument up to a large enough type *)
                  get_Zcast_up_if_needed (Some t') (Some t))
              | Z_shiftl offset
                => (** N.B. We must cast the expression up to a large
                       enough type to fit 2^offset (importantly, not
                       just 2^offset-1), because C considers it to be
                       undefined behavior to shift >= width of the
                       type.  We should probably figure out how to not
                       generate these things in the first place...

                       N.B. We make sure that we only left-shift
                       unsigned values, since shifting into the sign
                       bit is undefined behavior. *)
                let rpre_out := match desired_type with
                                | Some rout => Some (int.union_zrange r[0~>2^offset] (int.unsigned_counterpart_of rout))
                                | None => Some (int.of_zrange_relaxed r[0~>2^offset]%zrange)
                                end in
                ((** We cast the result down to the specified type, if needed *)
                  get_Zcast_down_if_needed desired_type rpre_out,
                  (** We cast the argument up to a large enough type *)
                  get_Zcast_up_if_needed rpre_out (Some t))
              | Z_lnot ty
                => ((* if the result is too big, we cast it down; we
                       don't need to upcast it because it'll get
                       picked up by implicit casts if necessary *)
                  get_Zcast_down_if_needed desired_type (Some ty),
                  (** always cast to the width of the type, unless we are already exactly that type (which the machinery in IR handles) *)
                  Some ty)
              | Z_value_barrier ty
                => ((* if the result is too big, we cast it down; we
                       don't need to upcast it because it'll get
                       picked up by implicit casts if necessary *)
                  get_Zcast_down_if_needed desired_type (Some ty),
                  (** implicit casts will cast the argument up if needed *)
                  None)
              | Z_bneg
                => ((* bneg is !, i.e., takes the argument to 1 if its not zero, and to zero if it is zero; so we don't ever need to cast *)
                  None, None)
              end.

      Local Instance CLanguageCasts : LanguageCasts :=
        {| bin_op_natural_output := C_bin_op_natural_output
           ; bin_op_casts := C_bin_op_casts
           ; un_op_casts := C_un_op_casts
           ; upcast_on_assignment := false
           ; upcast_on_funcall := false
           ; explicit_pointer_variables := false
        |}.

      (** Top-level printing functions *)

      Definition to_function_lines
                 {language_naming_conventions : language_naming_conventions_opt}
                 {skip_typedefs : skip_typedefs_opt}
                 (internal_static : bool) (static : bool) (all_static : bool) (inline : bool) (prefix : string) (name : string)
                 {t}
                 (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * expr)
        : list string
        := let '(args, rets, body) := f in
           (((((if static then "static " else "")
                 ++ (if inline then FIAT_INLINE prefix ++ " " else "")
                 ++ "void "
                 ++ name ++ "("
                 ++ (String.concat ", " (to_retarg_list prefix rets ++ to_arg_list_for_each_lhs_of_arrow prefix args))
                 ++ ") {")%string)
               :: (List.map (fun s => "  " ++ s)%string (to_strings internal_static prefix body)))
              ++ ["}"])%list.

      (** In C, there is no munging of return arguments (they remain
          passed by pointers), so all variables are live *)
      Local Instance : consider_retargs_live_opt := fun _ _ _ => true.
      Local Instance : rename_dead_opt := fun s => s.
      (** In C we do want to lift declarations to the top, to comply
          with ISO C90 *)
      Local Instance : lift_declarations_opt := true.

      Definition ToFunctionLines
                 {absint_opts : AbstractInterpretation.Options}
                 {relax_zrange : relax_zrange_opt}
                 {language_naming_conventions : language_naming_conventions_opt}
                 {documentation_options : documentation_options_opt}
                 {output_options : output_options_opt}
                 (machine_wordsize : Z)
                 (do_bounds_check : bool) (internal_static : bool) (static : bool) (all_static : bool) (inline : bool) (prefix : string) (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.base.option.interp (type.final_codomain t))
                 (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                 (outtypedefs : base_var_typedef_data (type.final_codomain t))
        : (list string * ident_infos) + string
        := match ExprOfPHOAS do_bounds_check e name_list inbounds intypedefs outtypedefs with
           | inl (indata, outdata, f)
             => inl ((["/*"]
                        ++ (List.map (fun s => if (String.length s =? 0)%nat then " *" else (" * " ++ s))%string (comment indata outdata))
                        ++ match input_bounds_to_string indata inbounds with
                           | nil => nil
                           | ls => [" * Input Bounds:"] ++ List.map (fun v => " *   " ++ v)%string ls
                           end
                        ++ match bound_to_string outdata outbounds with
                           | nil => nil
                           | ls => [" * Output Bounds:"] ++ List.map (fun v => " *   " ++ v)%string ls
                           end
                        ++ [" */"]
                        ++ to_function_lines internal_static static all_static inline prefix name (indata, outdata, f))%list,
                     ident_infos.collect_all_infos f intypedefs outtypedefs)
           | inr nil
             => inr ("Unknown internal error in converting " ++ name ++ " to C")%string
           | inr [err]
             => inr ("Error in converting " ++ name ++ " to C:" ++ String.NewLine ++ err)%string
           | inr errs
             => inr ("Errors in converting " ++ name ++ " to C:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
           end.

      Definition ToFunctionString
                 {absint_opts : AbstractInterpretation.Options}
                 {relax_zrange : relax_zrange_opt}
                 {language_naming_conventions : language_naming_conventions_opt}
                 {documentation_options : documentation_options_opt}
                 {output_options : output_options_opt}
                 (machine_wordsize : Z)
                 (do_bounds_check : bool) (internal_static : bool) (static : bool) (all_static : bool) (inline : bool) (prefix : string) (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.option.interp (type.base (type.final_codomain t)))
                 (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
                 (outtypedefs : base_var_typedef_data (type.final_codomain t))
        : (string * ident_infos) + string
        := match ToFunctionLines machine_wordsize do_bounds_check internal_static static all_static inline prefix name e comment name_list inbounds outbounds intypedefs outtypedefs with
           | inl (ls, used_types) => inl (LinesToString ls, used_types)
           | inr err => inr err
           end.

      Definition OutputCAPI : OutputLanguageAPI :=
        {|
          ToString.comment_block := comment_block;

          ToString.comment_file_header_block := comment_block;

          ToString.ToFunctionLines := @ToFunctionLines;

          ToString.header := @String.header;

          ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];

          (** We handle value_barrier specially *)
          ToString.strip_special_infos machine_wordsize infos
          := ident_info_with_value_barrier infos IntSet.empty;

        |}.
    End C.
    Notation ToFunctionLines := C.ToFunctionLines.
    Notation ToFunctionString := C.ToFunctionString.
    Notation OutputCAPI := C.OutputCAPI.
  End ToString.
End Compilers.
