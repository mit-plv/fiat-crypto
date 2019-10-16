From Coq Require Import ZArith.ZArith MSets.MSetPositive FSets.FMapPositive
     Strings.String Strings.Ascii Bool.Bool Lists.List.
From Crypto.Util Require Import
     ListUtil
     Strings.String Strings.Decimal Strings.HexString Strings.Show
     ZRange ZRange.Operations ZRange.Show
     Option OptionList Bool.Equality.

From Crypto Require Import IR Stringification.Language AbstractInterpretation.

Import ListNotations.

Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Module IR := IR.Compilers.ToString.IR.
Module ToString := Stringification.Language.Compilers.ToString.

Module Rust.

  Definition header : string :=
    "#![allow(unused_parens)]" ++ String.NewLine ++
    "#[allow(non_camel_case_types)]" ++ String.NewLine.

  (* Header imports and type defs *)
  (* TODO thread static flag in order to append pub *)
  Definition typedef_header (static : bool) (prefix : string) (bitwidths_used : PositiveSet.t)
    : list string
    := let type_prefix := ((if static then "type " else "pub type ") ++ prefix)%string in
       ([header]
          ++ (if PositiveSet.mem 1 bitwidths_used
              then [type_prefix ++ "u1 = u8;"; (* C: typedef unsigned char prefix_uint1 *)
                      type_prefix ++ "i1 = i8;" ]%string (* C: typedef signed char prefix_int1 *)
              else [])
          ++ (if PositiveSet.mem 2 bitwidths_used
              then [type_prefix ++ "u2 = u8;";
                      type_prefix ++ "i2 = i8;" ]%string
              else [])
          ++ (if PositiveSet.mem 128 bitwidths_used
              then [type_prefix ++ "u128 = u128;"; (* Since 128 bit integers exist in (nightly) rust consider removing the *)
                      (* type synonym and extending stdint_ditwidths *)
                      type_prefix ++ "i128 = i128;"]%string
              else []))%list.

  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
  Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).


  Definition int_type_to_string (prefix : string) (t : ToString.int.type) : string :=
    ((if is_special_bitwidth (ToString.int.bitwidth_of t) then prefix else "")
       ++ (if ToString.int.is_unsigned t then "u" else "i")
       ++ decimal_string_of_Z (ToString.int.bitwidth_of t))%string.


  (* Instead of "macros for minimum-width integer constants" we tried to
     use numeric casts in Rust. It turns out that it wasn't needed an Rust
     will figure out the types of the litterals, so disabling this for
     now *)
  Definition cast_literal (prefix : string) (t : ToString.int.type) : option string :=
    if Z.ltb (ToString.int.bitwidth_of t) 8
    then None
    else None.


  (* Zoe: In fiat-crypto C functions are void and as such, they receive
     pointers to the result as argumnets. The C code before calling a
     function, declares uninitializedinteger pointers and passes them as
     arguments.  In Rust to do that, we declare an initialized (to 0)
     mutable, and pass a mutable reference to the callee.

     In the longer term, we should examine whether we should use
     non-void functions in Rust and just return the result *)

  Definition primitive_type_to_string (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    match t with
    | IR.type.Zptr => "&mut "
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string prefix int_t
           | None => "ℤ" (* XXX what is this unicode symbol?? *)
           end.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t, cast_literal prefix (ToString.int.of_zrange_relaxed r[v ~> v]) with
    | IR.type.Z, Some cast => "(" ++ HexString.of_Z v ++ cast ++ ")"
    | IR.type.Z, None => (* just print hex value, no cast *) HexString.of_Z v
    | IR.type.Zptr, _ => "#error ""literal address " ++ HexString.of_Z v ++ """;"
    end.

  Import IR.Notations.

  Fixpoint arith_to_string (prefix : string) {t} (e : IR.arith_expr t) : string
    := match e with
       (* integer literals *)
       | (IR.literal v @@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@ IR.Var _ v) => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
       (* (de)referencing *)
       | (IR.Addr @@ IR.Var _ v) => "&mut " ++ v (* borrow a mutable ref to v *)
       | (IR.Dereference @@ e) => "( *" ++ arith_to_string prefix e ++ " )"
       (* bitwise operations *)
       | (IR.Z_shiftr offset @@ e) =>
         "(" ++ arith_to_string prefix e ++ " >> " ++ decimal_string_of_Z offset ++ ")"
       | (IR.Z_shiftl offset @@ e) =>
         "(" ++ arith_to_string prefix e ++ " << " ++ decimal_string_of_Z offset ++ ")"
       | (IR.Z_land @@ (e1, e2)) =>
         "(" ++ arith_to_string prefix e1 ++ " & " ++ arith_to_string prefix e2 ++ ")"
       | (IR.Z_lor @@ (e1, e2)) =>
         "(" ++ arith_to_string prefix e1 ++ " | " ++ arith_to_string prefix e2 ++ ")"
       | (IR.Z_lnot _ @@ e) => "(!" ++ arith_to_string prefix e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " + " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_mul @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " * " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_sub @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " - " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_opp @@ e) => "(-" ++ arith_to_string prefix e ++ ")" (* arithmetic negation *)
       | (IR.Z_bneg @@ e) => "(!" ++ arith_to_string prefix e ++ ")" (* logical negation. XXX this has different semantics for numbers <>
                                                                        0 or 1 than it did before *)
       | (IR.Z_mul_split lg2s @@ args) =>
         prefix
           ++ "mulx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (IR.Z_add_with_get_carry lg2s @@ args) =>
         prefix
           ++ "addcarryx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (IR.Z_sub_with_get_borrow lg2s @@ args) =>
         prefix
           ++ "subborrowx_u"
           ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
       | (IR.Z_zselect ty @@ args) =>
         prefix
           ++ "cmovznz_"
           ++ (if ToString.int.is_unsigned ty then "u" else "")
           ++ decimal_string_of_Z (ToString.int.bitwidth_of ty) ++ "(" ++ @arith_to_string prefix _ args ++ ")"
       | (IR.Z_static_cast int_t @@ e) =>
         "(" ++ arith_to_string prefix e ++ " as " ++ primitive_type_to_string prefix IR.type.Z (Some int_t) ++ ")"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string prefix a ++ ", " ++ arith_to_string prefix b
       | (IR.Z_add_modulo @@ (x1, x2, x3)) => "#error addmodulo;"
       | (IR.List_nth _ @@ _)
       | (IR.Addr @@ _)
       | (IR.Z_add @@ _)
       | (IR.Z_mul @@ _)
       | (IR.Z_sub @@ _)
       | (IR.Z_land @@ _)
       | (IR.Z_lor @@ _)
       | (IR.Z_add_modulo @@ _) => "#error bad_arg;"
       | TT => "#error tt;"
       end%string%Cexpr.

  Fixpoint stmt_to_string (prefix : string) (e : IR.stmt) : string :=
    match e with
    | IR.Call val => arith_to_string prefix val ++ ";"
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      "let " ++ name ++ ": " ++ primitive_type_to_string prefix t sz ++ " = " ++ arith_to_string prefix val ++ ";"
    | IR.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string prefix val ++ ";" *)
      "#error trying to assign value to non-mutable variable;"
    | IR.AssignZPtr name sz val =>
      "*" ++ name ++ " = " ++ arith_to_string prefix val ++ ";"
    | IR.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type *)
      "let mut " ++ name ++ ": " ++ primitive_type_to_string prefix t sz ++ " = 0;"
    | IR.AssignNth name n val =>
      name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string prefix val ++ ";"
    end.

  Definition to_strings (prefix : string) (e : IR.expr) : list string :=
    List.map (stmt_to_string prefix) e.

  Import Rewriter.Language.Language.Compilers Crypto.Language.API.Compilers IR.OfPHOAS.
  Local Notation tZ := (base.type.type_base base.type.Z).

  Inductive Mode := In | Out.


  (* This would have been nice, but coercions don't work *)
  (* Module Base := Rewriter.Language.Language.Compilers.base. *)

  Fixpoint to_base_arg_list (prefix : string) (mode : Mode) {t} : ToString.OfPHOAS.base_var_data t -> list string :=
    match t return base_var_data t -> _ with
    | tZ =>
      let typ := match mode with In => IR.type.Z | Out => IR.type.Zptr end in
      fun '(n, r) => [n ++ ": " ++ primitive_type_to_string prefix typ r]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list prefix mode va ++ to_base_arg_list prefix mode vb)%list
    | base.type.list tZ =>
      fun '(n, r, len) =>
        match mode with
        | In => (* arrays for inputs are immutable borrows *)
          [ n ++ ": " ++
              "&[" ++ primitive_type_to_string prefix IR.type.Z r  ++
              "; " ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ]
        | Out => (* arrays for outputs are mutable borrows *)
          [ n ++ ": " ++
              "&mut [" ++ primitive_type_to_string prefix IR.type.Z r ++
              "; " ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ]
        end
    | base.type.list _ => fun _ => ["#error ""complex list"";"]
    | base.type.option _ => fun _ => ["#error option;"]
    | base.type.unit => fun _ => ["#error unit;"]
    | base.type.type_base t => fun _ => ["#error " ++ show false t ++ ";"]%string
    end%string.

  Definition to_arg_list (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list prefix mode
    | type.arrow _ _ => fun _ => ["#error arrow;"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list prefix In x ++ @to_arg_list_for_each_lhs_of_arrow prefix d xs
       end%list.

  (* Used in comment *)
  Fixpoint bound_to_string {t : base.type} : var_data (type.base t) -> Compilers.ZRange.type.base.option.interp t -> list string :=
    match t return var_data (type.base t) -> Compilers.ZRange.type.base.option.interp t -> list string with
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
               ++ match Compilers.ZRange.type.base.option.lift_Some arg with
                  | Some arg => show false arg
                  | None => show false arg
                  end]%string
    | base.type.option _
    | base.type.unit
    | base.type.type_base _
      => fun _ _ => []
    end%list.

  (* Used in comment *)
  Fixpoint input_bounds_to_string {t}
    : type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t -> list string :=
    match t return type.for_each_lhs_of_arrow var_data t ->
                   type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t -> list string
    with
    | type.base t => fun _ _ => nil
    | type.arrow (type.base s) d =>
      fun '(v, vs) '(arg, args) =>
        (bound_to_string v arg)
          ++ @input_bounds_to_string d vs args
    | type.arrow s d =>
      fun '(absurd, _) => match absurd : Empty_set with end
    end%list.


  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  Definition Rust_bin_op_conversion
             (desired_type : option ToString.int.type)
             (args : arith_expr_for (type.base (tZ * tZ)))
    : arith_expr_for (type.base (tZ * tZ)) * option ToString.int.type :=
    match desired_type with
    | None => (args, None)
    | Some dt =>
      let '((e1, t1), (e2, t2)) := args in
      match t1, t2 with
      | None, _ | _, None => (args, None)
      | Some t1', Some t2' =>
        let ct := ToString.int.union t1' t2' in
        let desired_type' := Some (ToString.int.union ct dt) in
        ((Zcast_up_if_needed desired_type' (e1, t1),
          Zcast_up_if_needed desired_type' (e2, t2)),
         desired_type')
      end
    end.

  Definition Rust_un_op_conversion (desired_type : option ToString.int.type)
             (arg : arith_expr_for (type.base tZ))
    : arith_expr_for (type.base tZ) :=
    let '(e, r) := arg in
    Zcast_up_if_needed desired_type (e, r).

  Definition Rust_result_upcast (desired_type : option ToString.int.type) (e : arith_expr_for (type.base tZ))
    : arith_expr_for (type.base tZ) :=
    Zcast_up_if_needed desired_type e.

  Local Instance CLanguageCasts : LanguageCasts :=
    {| bin_op_conversion := Rust_bin_op_conversion;
       un_op_conversion := Rust_un_op_conversion;
       result_upcast := Rust_result_upcast
    |}.

  Definition to_function_lines (static : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    ("#[inline]" ++ String.NewLine ++ (if static then "fn " else "pub fn ") ++ name ++
      "(" ++ String.concat ", " (to_arg_list prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow prefix args) ++
      ") -> () {")%string :: (List.map (fun s => "  " ++ s)%string (to_strings prefix body)) ++ ["}"%string]%list.

  Definition ToFunctionLines (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
             {t}
             (e : API.Expr t)
             (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
             (name_list : option (list string))
             (inbounds : type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t)
             (outbounds : Compilers.ZRange.type.base.option.interp (type.final_codomain t))
    : (list string * ToString.ident_infos) + string :=
    match ExprOfPHOAS do_bounds_check e name_list inbounds with
    | inl (indata, outdata, f) =>
      inl ((["/*"%string]
              ++ (List.map (fun s => if (String.length s =? 0)%nat then " *" else (" * " ++ s))%string (comment indata outdata))
              ++ [" * Input Bounds:"%string]
              ++ List.map (fun v => " *   "%string ++ v)%string (input_bounds_to_string indata inbounds)
              ++ [" * Output Bounds:"%string]
              ++ List.map (fun v => " *   "%string ++ v)%string (bound_to_string outdata outbounds)
              ++ [" */"%string]
              ++ to_function_lines static prefix name (indata, outdata, f))%list,
           (* Zoe: This is a function in the Stringification.C file,
              consider moving this elsewhere? *)
           IR.ident_infos.collect_infos f)
    | inr nil =>
      inr ("Unknown internal error in converting " ++ name ++ " to Rust")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputRustAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := List.map (fun line => "/* " ++ line ++ " */")%string;
       ToString.ToFunctionLines := ToFunctionLines;
       ToString.typedef_header := typedef_header |}.

End Rust.
