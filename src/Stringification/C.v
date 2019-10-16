Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
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
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope zrange_scope. Local Open Scope Z_scope.


Module Compilers.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Export Language.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.Compilers.
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
      Module String.
        Definition typedef_header (static : bool) (prefix : string) (bitwidths_used : PositiveSet.t)
        : list string
          := (["#include <stdint.h>"]
                ++ (if PositiveSet.mem 1 bitwidths_used
                    then ["typedef unsigned char " ++ prefix ++ "uint1;";
                            "typedef signed char " ++ prefix ++ "int1;"]%string
                    else [])
                ++ (if PositiveSet.mem 128 bitwidths_used
                    then ["typedef signed __int128 " ++ prefix ++ "int128;";
                            "typedef unsigned __int128 " ++ prefix ++ "uint128;"]%string
                    else [])
                ++ [""
                    ; "#if (-1 & 3) != 3"
                    ; "#error ""This code only works on a two's complement system"""
                    ; "#endif"])%list.

        Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
        Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).

        Module int.
          Module type.
            Definition to_string (prefix : string) (t : int.type) : string
              := ((if is_special_bitwidth (int.bitwidth_of t) then prefix else "")
                    ++ (if int.is_unsigned t then "u" else "")
                    ++ "int"
                    ++ decimal_string_of_Z (int.bitwidth_of t)
                    ++ (if is_special_bitwidth (int.bitwidth_of t) then "" else "_t"))%string.
            Definition to_literal_macro_string (t : int.type) : option string
              := if Z.ltb (int.bitwidth_of t) 8
                 then None
                 else Some ((if int.is_unsigned t then "U" else "")
                              ++ "INT"
                              ++ decimal_string_of_Z (int.bitwidth_of t)
                              ++ "_C")%string.
          End type.
        End int.

        Module type.
          Module primitive.
            Definition to_string (prefix : string) (t : type.primitive) (r : option int.type) : string
              := match r with
                 | Some int_t => int.type.to_string prefix int_t
                 | None => "ℤ"
                 end ++ match t with
                        | type.Zptr => "*"
                        | type.Z => ""
                        end.
          End primitive.
        End type.
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

      Fixpoint arith_to_string (prefix : string) {t} (e : arith_expr t) : string
        := match e with
           | (literal v @@ _) => primitive.to_string prefix type.Z v
           | (List_nth n @@ Var _ v)
             => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
           | (Addr @@ Var _ v) => "&" ++ v
           | (Dereference @@ e) => "( *" ++ @arith_to_string prefix _ e ++ " )"
           | (Z_shiftr offset @@ e)
             => "(" ++ @arith_to_string prefix _ e ++ " >> " ++ decimal_string_of_Z offset ++ ")"
           | (Z_shiftl offset @@ e)
             => "(" ++ @arith_to_string prefix _ e ++ " << " ++ decimal_string_of_Z offset ++ ")"
           | (Z_land @@ (e1, e2))
             => "(" ++ @arith_to_string prefix _ e1 ++ " & " ++ @arith_to_string prefix _ e2 ++ ")"
           | (Z_lor @@ (e1, e2))
             => "(" ++ @arith_to_string prefix _ e1 ++ " | " ++ @arith_to_string prefix _ e2 ++ ")"
           | (Z_add @@ (x1, x2))
             => "(" ++ @arith_to_string prefix _ x1 ++ " + " ++ @arith_to_string prefix _ x2 ++ ")"
           | (Z_mul @@ (x1, x2))
             => "(" ++ @arith_to_string prefix _ x1 ++ " * " ++ @arith_to_string prefix _ x2 ++ ")"
           | (Z_sub @@ (x1, x2))
             => "(" ++ @arith_to_string prefix _ x1 ++ " - " ++ @arith_to_string prefix _ x2 ++ ")"
           | (Z_opp @@ e)
             => "(-" ++ @arith_to_string prefix _ e ++ ")"
           | (Z_lnot _ @@ e)
             => "(~" ++ @arith_to_string prefix _ e ++ ")"
           | (Z_bneg @@ e)
             => "(!" ++ @arith_to_string prefix _ e ++ ")"
           | (Z_mul_split lg2s @@ args)
             => prefix
                 ++ "mulx_u"
                 ++ decimal_string_of_Z lg2s ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_add_with_get_carry lg2s @@ args)
             => prefix
                 ++ "addcarryx_u"
                 ++ decimal_string_of_Z lg2s ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_sub_with_get_borrow lg2s @@ args)
             => prefix
                 ++ "subborrowx_u"
                 ++ decimal_string_of_Z lg2s ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_zselect ty @@ args)
             => prefix
                 ++ "cmovznz_"
                 ++ (if int.is_unsigned ty then "u" else "")
                 ++ decimal_string_of_Z (int.bitwidth_of ty) ++ "(" ++ @arith_to_string prefix _ args ++ ")"
           | (Z_add_modulo @@ (x1, x2, x3)) => "#error addmodulo;"
           | (Z_static_cast int_t @@ e)
             => "(" ++ String.type.primitive.to_string prefix type.Z (Some int_t) ++ ")"
                    ++ @arith_to_string prefix _ e
           | Var _ v => v
           | Pair A B a b
             => @arith_to_string prefix A a ++ ", " ++ @arith_to_string prefix B b
           | (List_nth _ @@ _)
           | (Addr @@ _)
           | (Z_add @@ _)
           | (Z_mul @@ _)
           | (Z_sub @@ _)
           | (Z_land @@ _)
           | (Z_lor @@ _)
           | (Z_add_modulo @@ _)
             => "#error bad_arg;"
           | TT
             => "#error tt;"
           end%core%Cexpr.

      Fixpoint stmt_to_string (prefix : string) (e : stmt) : string
        := match e with
           | Call val
             => arith_to_string prefix val ++ ";"
           | Assign true t sz name val
             => String.type.primitive.to_string prefix t sz ++ " " ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
           | Assign false _ sz name val
             => name ++ " = " ++ arith_to_string prefix val ++ ";"
           | AssignZPtr name sz val
             => "*" ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
           | DeclareVar t sz name
             => String.type.primitive.to_string prefix t sz ++ " " ++ name ++ ";"
           | AssignNth name n val
             => name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string prefix val ++ ";"
           end.
      Definition to_strings (prefix : string) (e : expr) : list string
        := List.map (stmt_to_string prefix) e.

      Import OfPHOAS.

      Fixpoint to_base_arg_list (prefix : string) {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | tZ
             => fun '(n, r) => [String.type.primitive.to_string prefix type.Z r ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (@to_base_arg_list prefix A va ++ @to_base_arg_list prefix B vb)%list
           | base.type.list tZ
             => fun '(n, r, len) => ["const " ++ String.type.primitive.to_string prefix type.Z r ++ " " ++ n ++ "[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]"]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.option _ => fun _ => ["#error option;"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.type_base t => fun _ => ["#error " ++ show false t ++ ";"]%string
           end.

      Definition to_arg_list (prefix : string) {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base t => to_base_arg_list prefix
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Fixpoint to_arg_list_for_each_lhs_of_arrow (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> _ with
           | type.base t => fun _ => nil
           | type.arrow s d
             => fun '(x, xs)
                => to_arg_list prefix x ++ @to_arg_list_for_each_lhs_of_arrow prefix d xs
           end%list.

      Fixpoint to_base_retarg_list prefix {t} : base_var_data t -> list string
        := match t return base_var_data t -> _ with
           | tZ
             => fun '(n, r) => [String.type.primitive.to_string prefix type.Zptr r ++ " " ++ n]
           | base.type.prod A B
             => fun '(va, vb) => (@to_base_retarg_list prefix A va ++ @to_base_retarg_list prefix B vb)%list
           | base.type.list tZ
             => fun '(n, r, len) => [String.type.primitive.to_string prefix type.Z r ++ " " ++ n ++ "[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]"]
           | base.type.list _ => fun _ => ["#error ""complex list"";"]
           | base.type.option _ => fun _ => ["#error option;"]
           | base.type.unit => fun _ => ["#error unit;"]
           | base.type.type_base t => fun _ => ["#error " ++ show false t ++ ";"]%string
           end.

      Definition to_retarg_list (prefix : string) {t} : var_data t -> list string
        := match t return var_data t -> _ with
           | type.base _ => to_base_retarg_list prefix
           | type.arrow _ _ => fun _ => ["#error arrow;"]
           end.

      Fixpoint bound_to_string {t : base.type} : var_data (type.base t) -> ZRange.type.base.option.interp t -> list string
        := match t return var_data (type.base t) -> ZRange.type.base.option.interp t -> list string with
           | tZ
             => fun '(name, _) arg
                => [(name ++ ": ")
                      ++ match arg with
                         | Some arg => show false arg
                         | None => show false arg
                         end]%string
           | base.type.prod A B
             => fun '(va, vb) '(a, b)
                => @bound_to_string A va a ++ @bound_to_string B vb b
           | base.type.list A
             => fun '(name, _, _) arg
                => [(name ++ ": ")
                      ++ match ZRange.type.base.option.lift_Some arg with
                         | Some arg => show false arg
                         | None => show false arg
                         end]%string
           | base.type.option _
           | base.type.unit
           | base.type.type_base _
             => fun _ _ => nil
           end%list.

      Fixpoint input_bounds_to_string {t} : type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> list string
        := match t return type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow ZRange.type.option.interp t -> list string with
           | type.base t => fun _ _ => nil
           | type.arrow (type.base s) d
             => fun '(v, vs) '(arg, args)
                => (bound_to_string v arg)
                     ++ @input_bounds_to_string d vs args
           | type.arrow s d
             => fun '(absurd, _) => match absurd : Empty_set with end
           end%list.




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

      Definition C_bin_op_conversion
                 (desired_type : option int.type)
                 (args : arith_expr_for (type.base (tZ * tZ)))
        : arith_expr_for (type.base (tZ * tZ)) * option int.type
        := match desired_type with
           | None => (args, None)
           | Some _
             => let '((e1, t1), (e2, t2)) := args in
                (* Zoe: internalized integer promotions *)
                let t1 := option_map integer_promote_type t1 in
                let t2 := option_map integer_promote_type t2 in
                match t1, t2 with
                | None, _ | _, None => (args, None)
                | Some t1', Some t2' =>
                  let args :=
                      if int.is_tighter_than t2' t1'
                      then (Zcast_up_if_needed desired_type (e1, t1), (e2, t2))
                      else ((e1, t1), Zcast_up_if_needed desired_type (e2, t2))
                  in
                  let '((e1, t1), (e2, t2)) := args in
                  let ct := (t1 <- t1; t2 <- t2; Some (C_common_type t1 t2))%option in
                  (args, ct)
                end
           end.

      Definition C_un_op_conversion (desired_type : option int.type)
                 (arg : arith_expr_for (type.base tZ))
        : arith_expr_for (type.base tZ) :=
        let '(e, r) := arg in
        let rin := option_map integer_promote_type r in
        Zcast_up_if_needed desired_type (e, rin).

      Local Instance CLanguageCasts : LanguageCasts :=
        {| bin_op_conversion := C_bin_op_conversion;
           un_op_conversion := C_un_op_conversion;
           result_upcast := fun _ e => e (* C doesn't need to upcast assignments/functions args*)
        |}.

      (** Top-level printing functions *)

      Definition to_function_lines (static : bool) (prefix : string) (name : string)
                 {t}
                 (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * expr)
        : list string
        := let '(args, rets, body) := f in
           (((((if static then "static " else "")
                 ++ "void "
                 ++ name ++ "("
                 ++ (String.concat ", " (to_retarg_list prefix rets ++ to_arg_list_for_each_lhs_of_arrow prefix args))
                 ++ ") {")%string)
               :: (List.map (fun s => "  " ++ s)%string (to_strings prefix body)))
              ++ ["}"])%list.

      Definition ToFunctionLines (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.base.option.interp (type.final_codomain t))
        : (list string * ident_infos) + string
        := match ExprOfPHOAS do_bounds_check e name_list inbounds with
           | inl (indata, outdata, f)
             => inl ((["/*"]
                        ++ (List.map (fun s => if (String.length s =? 0)%nat then " *" else (" * " ++ s))%string (comment indata outdata))
                        ++ [" * Input Bounds:"]
                        ++ List.map (fun v => " *   " ++ v)%string (input_bounds_to_string indata inbounds)
                        ++ [" * Output Bounds:"]
                        ++ List.map (fun v => " *   " ++ v)%string (bound_to_string outdata outbounds)
                        ++ [" */"]
                        ++ to_function_lines static prefix name (indata, outdata, f))%list,
                     ident_infos.collect_infos f)
           | inr nil
             => inr ("Unknown internal error in converting " ++ name ++ " to C")%string
           | inr [err]
             => inr ("Error in converting " ++ name ++ " to C:" ++ String.NewLine ++ err)%string
           | inr errs
             => inr ("Errors in converting " ++ name ++ " to C:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
           end.

      Definition ToFunctionString (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
                 {t}
                 (e : @Compilers.expr.Expr base.type ident.ident t)
                 (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
                 (name_list : option (list string))
                 (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
                 (outbounds : ZRange.type.option.interp (type.base (type.final_codomain t)))
        : (string * ident_infos) + string
        := match ToFunctionLines do_bounds_check static prefix name e comment name_list inbounds outbounds with
           | inl (ls, used_types) => inl (LinesToString ls, used_types)
           | inr err => inr err
           end.

      Definition OutputCAPI : OutputLanguageAPI :=
        {|
          comment_block s
          := List.map (fun line => "/* " ++ line ++ " */")%string s;

          ToString.ToFunctionLines := ToFunctionLines;

          ToString.typedef_header := String.typedef_header
        |}.
    End C.
    Notation ToFunctionLines := C.ToFunctionLines.
    Notation ToFunctionString := C.ToFunctionString.
    Notation OutputCAPI := C.OutputCAPI.
  End ToString.
End Compilers.
