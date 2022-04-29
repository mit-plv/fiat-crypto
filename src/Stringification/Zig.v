From Coq Require Import ZArith.ZArith MSets.MSetPositive FSets.FMapPositive
     Strings.String Strings.Ascii Bool.Bool Lists.List Strings.HexString.
From Crypto.Util Require Import
     ListUtil
     Strings.String Strings.Decimal Strings.Show
     ZRange.Operations ZRange.Show
     OptionList Bool.Equality.
Require Import Crypto.Util.Option.

Require Import Crypto.Util.ZRange.

From Crypto Require Import IR Stringification.Language AbstractInterpretation.ZRange.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Import IR.Compilers.ToString.
Import Stringification.Language.Compilers.
Import Stringification.Language.Compilers.Options.
Import Stringification.Language.Compilers.ToString.
Import Stringification.Language.Compilers.ToString.int.Notations.

Module Zig.
  Definition comment_module_header_block := List.map (fun line => "// " ++ line)%string.
  Definition comment_block := List.map (fun line => "// " ++ line)%string.

  (* Zig natively supports any integer size between 0 and 4096 bits.
     So, we never need to define our own types. *)
  Definition int_type_to_string_opt_typedef {skip_typedefs : skip_typedefs_opt} {language_naming_conventions : language_naming_conventions_opt} (typedef_private : bool) (prefix : string) (t : ToString.int.type) (typedef : option string) : string :=
    match (if skip_typedefs then None else typedef) with
    | None => (if int.is_unsigned t then "u" else "i") ++ Decimal.Z.to_string (ToString.int.bitwidth_of t)
    | Some typedef => format_typedef_name prefix typedef_private typedef
    end.
  Definition int_type_to_string {language_naming_conventions : language_naming_conventions_opt} (t : ToString.int.type) : string :=
    int_type_to_string_opt_typedef (skip_typedefs:=true) false "" t None.

  Definition primitive_type_to_string_opt_typedef
             {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt}
             (all_private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) (typedef : option string) : string :=
    match t with
    | IR.type.Zptr => "*"
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string_opt_typedef all_private prefix int_t typedef
           | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
           end.
  Definition primitive_type_to_string {language_naming_conventions : language_naming_conventions_opt} (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    primitive_type_to_string_opt_typedef (skip_typedefs:=true) false "" t r None.

  Definition primitive_array_type_to_string
             {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt}
             (all_private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) (len : nat) (typedef : option string) : string :=
    match (if skip_typedefs then None else typedef) with
    | Some typedef => format_typedef_name prefix all_private typedef
    | None => "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]" ++
                  primitive_type_to_string t r
    end.

  Definition make_typedef
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             (prefix : string) (private : bool)
             (typedef : typedef_info)
    : list string
    := let '(name, (ty, array_len), description) := name_and_type_and_describe_typedef prefix private typedef in
       ((comment_block description)
          ++ [(if private then "const " else "pub const ")
                ++ name ++ " = " ++
                let ty_string := match ty with
                                 | Some ty => int_type_to_string ty
                                 | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
                                 end in
                match array_len with
                | None (* just an integer *) => ty_string
                | Some None (* unknown array length *) => "*" ++ ty_string
                | Some (Some len) => "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]" ++ ty_string
                end
                ++ ";"]%string)%list.

  Definition header
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {package_namev : package_name_opt}
             {class_namev : class_name_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z) (internal_private : bool) (private : bool) (prefix : string) (infos : ToString.ident_infos)
             (typedef_map : list typedef_info)
    : list string
    := (["";
         "const std = @import(""std"");";
         "const mode = @import(""builtin"").mode; // Checked arithmetic is disabled in non-debug modes to avoid side channels";
         "";
         "inline fn cast(comptime DestType: type, target: anytype) DestType {";
         "    if (@typeInfo(@TypeOf(target)) == .Int) {";
         "        const dest = @typeInfo(DestType).Int;";
         "        const source = @typeInfo(@TypeOf(target)).Int;";
         "        if (dest.bits < source.bits) {";
         "            return @bitCast(DestType, @truncate(std.meta.Int(source.signedness, dest.bits), target));";
         "        } else {";
         "            return @bitCast(DestType, @as(std.meta.Int(source.signedness, dest.bits), target));";
         "        }";
         "    }";
         "    return @as(DestType, target);";
         "}"]
          ++ (if skip_typedefs
              then []
              else List.flat_map
                     (fun td_name =>
                        match List.find (fun '(name, _, _, _) => (td_name =? name)%string) typedef_map with
                        | Some td_info => [""] ++ make_typedef prefix private td_info
                        | None => ["@compilerError(""Could not find typedef info for '" ++ td_name ++ "'"");"]%string
                        end%list)
                     (typedefs_used infos)))%list.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t with
    | IR.type.Z => HexString.of_Z v (* Zig can automatically figure out the size of integer literals *)
    | IR.type.Zptr => "@compilerError(""literal address " ++ HexString.of_Z v ++ """);"
    end.

  Import IR.Notations.

  Fixpoint arith_to_string
           {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
           (prefix : string) {t} (e : IR.arith_expr t) : string
    := let special_name_ty name ty := ToString.format_special_function_name_ty internal_private prefix name ty in
       let special_name name bw := ToString.format_special_function_name internal_private prefix name false(*unsigned*) bw in
       match e with
       (* integer literals *)
       | (IR.literal v @@@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@@ IR.Var _ v) => "(" ++ v ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "])"
       (* (de)referencing *)
       | (IR.Addr @@@ IR.Var _ v) => "&" ++ v
       | (IR.Dereference @@@ e) => "( " ++ arith_to_string internal_private prefix e ++ ".* )"
       (* bitwise operations *)
       | (IR.Z_shiftr offset @@@ e) =>
         "(" ++ arith_to_string internal_private prefix e ++ " >> " ++ Decimal.Z.to_string offset ++ ")"
       | (IR.Z_shiftl offset @@@ e) =>
         "(" ++ arith_to_string internal_private prefix e ++ " << " ++ Decimal.Z.to_string offset ++ ")"
       | (IR.Z_land @@@ (e1, e2)) =>
         "(" ++ arith_to_string internal_private prefix e1 ++ " & " ++ arith_to_string internal_private prefix e2 ++ ")"
       | (IR.Z_lor @@@ (e1, e2)) =>
         "(" ++ arith_to_string internal_private prefix e1 ++ " | " ++ arith_to_string internal_private prefix e2 ++ ")"
       | (IR.Z_lxor @@@ (e1, e2)) =>
         "(" ++ arith_to_string internal_private prefix e1 ++ " ^ " ++ arith_to_string internal_private prefix e2 ++ ")"
       | (IR.Z_lnot _ @@@ e) => "(~" ++ arith_to_string internal_private prefix e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " + " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_mul @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " * " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_sub @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " - " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_bneg @@@ e) => "(~" ++ arith_to_string internal_private prefix e ++ ")"
       | (IR.Z_mul_split lg2s @@@ args) =>
         special_name "mulx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_add_with_get_carry lg2s @@@ args) =>
         special_name "addcarryx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_sub_with_get_borrow lg2s @@@ args) =>
         special_name "subborrowx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_zselect ty @@@ args) =>
         special_name_ty "cmovznz" ty ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_value_barrier ty @@@ args) =>
         special_name_ty "value_barrier" ty ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_static_cast int_t @@@ e) =>
         "cast(" ++ primitive_type_to_string IR.type.Z (Some int_t) ++ ", " ++ arith_to_string internal_private prefix e ++ ")"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string internal_private prefix a ++ ", " ++ arith_to_string internal_private prefix b
       | (IR.Z_add_modulo @@@ (x1, x2, x3)) => "@compilerError(""addmodulo"");"
       | (IR.List_nth _ @@@ _)
       | (IR.Addr @@@ _)
       | (IR.Z_add @@@ _)
       | (IR.Z_mul @@@ _)
       | (IR.Z_sub @@@ _)
       | (IR.Z_land @@@ _)
       | (IR.Z_lor @@@ _)
       | (IR.Z_lxor @@@ _)
       | (IR.Z_add_modulo @@@ _) => "@compilerError(""bad_arg"");"
       | IR.TT => "@compilerError(""tt"");"
       end%string%Cexpr.

  Definition stmt_to_string
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (prefix : string) (e : IR.stmt) : string :=
    match e with
    | IR.Call val => arith_to_string internal_private prefix val ++ ";"
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      "const " ++ name ++ " = " ++ arith_to_string internal_private prefix val ++ ";"
    | IR.Assign false _ sz name val =>
    (* code : name ++ " = " ++ arith_to_string internal_private prefix val ++ ";" *)
      "@compilerError(""trying to assign value to non-mutable variable"");"
    | IR.AssignZPtr name sz val =>
      name ++ ".* = " ++ arith_to_string internal_private prefix val ++ ";"
    | IR.DeclareVar t sz name =>
      "var " ++ name ++ ": " ++ primitive_type_to_string t sz ++ " = undefined;"
    | IR.Comment lines _ =>
      String.concat String.NewLine (comment_block (ToString.preprocess_comment_block lines))
    | IR.AssignNth name n val =>
      name ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "] = " ++ arith_to_string internal_private prefix val ++ ";"
    end.

  Definition to_strings {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool) (prefix : string) (e : IR.expr) : list string :=
    List.map (stmt_to_string internal_private prefix) e.

  Import Rewriter.Language.Language.Compilers Crypto.Language.API.Compilers IR.OfPHOAS.
  Local Notation tZ := (base.type.type_base base.type.Z).

  Inductive Mode := In | Out.

  Fixpoint to_base_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) (mode : Mode) {t} : ToString.OfPHOAS.base_var_data t -> list string :=
    match t return base_var_data t -> _ with
    | tZ =>
      let typ := match mode with In => IR.type.Z | Out => IR.type.Zptr end in
      fun '(n, is_ptr, r, typedef) => [n ++ ": " ++ primitive_type_to_string_opt_typedef all_private prefix typ r typedef]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list internal_private all_private prefix mode va ++ to_base_arg_list internal_private all_private prefix mode vb)%list
    | base.type.list tZ =>
      fun '(n, r, len, typedef) =>
        let modifier := match mode with
                        | In => (* arrays for inputs are immutable *) ""
                        | Out => (* arrays for outputs are mutable *) "*"
                        end in
        [ n ++ ": " ++ modifier ++ primitive_array_type_to_string all_private prefix IR.type.Z r len typedef ]
    | base.type.list _ => fun _ => ["@compilerError(""complex list"");"]
    | base.type.option _ => fun _ => ["@compilerError(""option"");"]
    | base.type.unit => fun _ => ["@compilerError(""unit"");"]
    | base.type.type_base t => fun _ => ["@compilerError(""" ++ show t ++ """);"]%string
    end%string.

  Definition to_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list internal_private all_private prefix mode
    | type.arrow _ _ => fun _ => ["@compilerError(""arrow"");"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list internal_private all_private prefix In x ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix xs
       end%list.

  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  Definition Zig_bin_op_natural_output
    : IR.Z_binop -> ToString.int.type * ToString.int.type -> ToString.int.type
    := fun idc '(t1, t2)
       => ToString.int.union t1 t2.

  Definition Zig_bin_op_casts
    : IR.Z_binop -> option ToString.int.type -> ToString.int.type * ToString.int.type -> option ToString.int.type * (option ToString.int.type * option ToString.int.type)
    := fun idc desired_type '(t1, t2)
       => match desired_type with
          | Some desired_type
            => let ct := ToString.int.union t1 t2 in
               let desired_type' := Some (ToString.int.union ct desired_type) in
               (Some desired_type,
                (get_Zcast_up_if_needed desired_type' (Some t1),
                 get_Zcast_up_if_needed desired_type' (Some t2)))
          | None => (None, (None, None))
          end.

  Definition Zig_un_op_casts
    : IR.Z_unop -> option ToString.int.type -> ToString.int.type -> option ToString.int.type * option ToString.int.type
    := fun idc desired_type t
       => match idc with
          | IR.Z_shiftr offset
            =>
            let t' := ToString.int.union_zrange r[0~>2^offset]%zrange t in
            ((** We cast the result down to the specified type, if needed *)
              get_Zcast_down_if_needed desired_type (Some t'),
              (** We cast the argument up to a large enough type *)
              get_Zcast_up_if_needed (Some t') (Some t))
          | IR.Z_shiftl offset
            =>
            let rpre_out := match desired_type with
                            | Some rout => Some (ToString.int.union_zrange r[0~>2^offset] (ToString.int.unsigned_counterpart_of rout))
                            | None => Some (ToString.int.of_zrange_relaxed r[0~>2^offset]%zrange)
                            end in
            ((** We cast the result down to the specified type, if needed *)
              get_Zcast_down_if_needed desired_type rpre_out,
              (** We cast the argument up to a large enough type *)
              get_Zcast_up_if_needed rpre_out (Some t))
          | IR.Z_lnot ty
            => (
              get_Zcast_down_if_needed desired_type (Some ty),
              (** always cast to the width of the type, unless we are already exactly that type (which the machinery in IR handles *)
              Some ty)
          | IR.Z_value_barrier ty
            => (
              get_Zcast_down_if_needed desired_type (Some ty),
              (** always cast to the width of the type, unless we are already exactly that type (which the machinery in IR handles *)
              Some ty)
          | IR.Z_bneg
            => ((* bneg is !, i.e., takes the argument to 1 if its not zero, and to zero if it is zero; so we don't ever need to cast *)
              None, None)
          end.

  Local Instance ZigLanguageCasts : LanguageCasts :=
    {| bin_op_natural_output := Zig_bin_op_natural_output
       ; bin_op_casts := Zig_bin_op_casts
       ; un_op_casts := Zig_un_op_casts
       ; upcast_on_assignment := true
       ; upcast_on_funcall := true
       ; explicit_pointer_variables := false
    |}.

  Definition to_function_lines {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (private : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    ((if private || inline then "inline fn " else "pub fn ") ++ name ++
      "(" ++ String.concat ", " (to_arg_list internal_private all_private prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix args) ++
      ") void {")%string :: (["    @setRuntimeSafety(mode == .Debug);"; ""]%string)%list ++ (List.map (fun s => "    " ++ s)%string (to_strings internal_private prefix body)) ++ ["}"%string]%list.

  (** In Zig, there is no munging of return arguments (they remain
      passed by pointers), so all variables are live *)
  Local Instance : consider_retargs_live_opt := fun _ _ _ => true.
  Local Instance : rename_dead_opt := fun s => s.
  (** No need to lift declarations to the top *)
  Local Instance : lift_declarations_opt := false.

  Definition ToFunctionLines
             {absint_opts : AbstractInterpretation.Options}
             {relax_zrange : relax_zrange_opt}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z)
             (do_bounds_check : bool) (internal_private : bool) (private : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
             {t}
             (e : API.Expr t)
             (comment : type.for_each_lhs_of_arrow var_data t -> var_data (type.base (type.final_codomain t)) -> list string)
             (name_list : option (list string))
             (inbounds : type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t)
             (outbounds : Compilers.ZRange.type.base.option.interp (type.final_codomain t))
             (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
             (outtypedefs : base_var_typedef_data (type.final_codomain t))
    : (list string * ToString.ident_infos) + string :=
    match ExprOfPHOAS do_bounds_check e name_list inbounds intypedefs outtypedefs with
    | inl (indata, outdata, f) =>
      inl (((List.map (fun s => if (String.length s =? 0)%nat then "///" else ("/// " ++ s))%string (comment indata outdata))
              ++ match input_bounds_to_string indata inbounds with
                 | nil => nil
                 | ls => ["/// Input Bounds:"] ++ List.map (fun v => "///   " ++ v)%string ls
                 end
              ++ match bound_to_string outdata outbounds with
                 | nil => nil
                 | ls => ["/// Output Bounds:"] ++ List.map (fun v => "///   " ++ v)%string ls
                 end
              ++ to_function_lines internal_private private all_private inline prefix name (indata, outdata, f))%list%string,
           IR.ident_infos.collect_all_infos f intypedefs outtypedefs)
    | inr nil =>
      inr ("Unknown internal error in converting " ++ name ++ " to Zig")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to Zig:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to Zig:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputZigAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := comment_block;
       ToString.comment_file_header_block := comment_module_header_block;
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := @header;
       ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];
       ToString.strip_special_infos machine_wordsize infos := infos |}.

End Zig.
