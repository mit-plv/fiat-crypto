From Coq Require Import ZArith.ZArith MSets.MSetPositive FSets.FMapPositive
     Strings.String Strings.Ascii Bool.Bool Lists.List Strings.HexString.
From Crypto.Util Require Import
     ListUtil
     Strings.String Strings.Decimal Strings.Show
     ZRange.Operations ZRange.Show
     OptionList Bool.Equality.
Require Import Crypto.Util.Option.
(* Work around COQBUG(https://github.com/coq/coq/issues/12251) *)
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

Module Java.
  Definition comment_block := List.map (fun line => "/* " ++ line ++ " */")%string.

  (* Header imports and type defs *)
  Definition header
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {package_namev : package_name_opt}
             {class_namev : class_name_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z) (internal_private : bool) (private : bool) (prefix : string) (infos : ToString.ident_infos)
             (typedef_map : list typedef_info)
  : list string
    (* N.B. We don't do anything with private; we always export everything *)
    := let bitwidths_used := ToString.bitwidths_used infos in
       (* Java class names are in mixed case *)
       ((["";
         "package " ++ package_name prefix ++ ";";
         "";
         "public final class " ++ class_name prefix ++ " {";
         (** Java doesn't have pointers, so we make them *)
         "";
         "static class Box<T> {";
         "  private T value;";
         "  public Box(T value) { this.value = value; }";
         "  public void set(T value) { this.value = value; }";
         "  public T get() { return this.value; }";
         "}";
         "";
         ""]%string)).
  Definition footer
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {package_namev : package_name_opt}
             {class_namev : class_name_opt}
             (machine_wordsize : Z) (internal_private : bool) (private : bool) (prefix : string) (infos : ToString.ident_infos)
    : list string
    := ["}"]%string.

  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [32; 64].
  Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).


  Definition int_type_to_string (use_class : bool) (prefix : string) (t : ToString.int.type) : string :=
    let bw := ToString.int.bitwidth_of t in
    if bw =? 1 (* we have some of these left over from carries guaranteed to be 0; we use int for them because that's the only thing that will typecheck.  This is a bit of a kludge *)
    then if use_class then "Integer" else "int"
    else if bw =? 8 then if use_class then "Byte" else "byte"
         else if bw =? 16 then if use_class then "Short" else "short"
              else if bw =? 32 then if use_class then "Integer" else "int"
                   else if bw =? 64 then if use_class then "Long" else "long"
                        else (prefix
                                ++ (if ToString.int.is_unsigned t then "uint" else "int")
                                ++ Decimal.Z.to_string (ToString.int.bitwidth_of t))%string.

  Definition primitive_type_to_string (use_class : bool) (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    match t with
    | IR.type.Zptr => fun t => "Box<" ++ t true ++">"
    | IR.type.Z => fun t => t use_class
    end%string
       (fun use_class
        => match r with
           | Some int_t => int_type_to_string use_class prefix int_t
           | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
           end).

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t with
    | IR.type.Z
      => (HexString.of_Z v)
           ++ if ToString.int.bitwidth_of (ToString.int.of_zrange_relaxed r[v ~> v]) >? 32
              then "L"
              else ""
    | IR.type.Zptr => "error_literal_address_" ++ HexString.of_Z v
    end%string.

  Import IR.Notations.

  Fixpoint arith_to_string
           {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
           (prefix : string)
           {t} (e : IR.arith_expr t)
    : string
    := let special_name_ty name ty := ToString.format_special_function_name_ty internal_private prefix name ty in
       let special_name name bw := ToString.format_special_function_name internal_private prefix name false(*unsigned*) bw in
       match e with
       (* integer literals *)
       | (IR.literal v @@@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@@ IR.Var _ v) => "(" ++ v ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "])"
       (* (de)referencing *)
       | (IR.Dereference @@@ e) => "(" ++ arith_to_string internal_private prefix e ++ ").get()"
       (* bitwise operations *)
       | (IR.Z_shiftr offset @@@ e) =>
         (* We assume that shift is always unsigned *)
         "(" ++ arith_to_string internal_private prefix e ++ " >>> " ++ Decimal.Z.to_string offset ++ ")"
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
       | (IR.Z_bneg @@@ e) => "(!/* TODO: FIX ME */ " ++ arith_to_string internal_private prefix e ++ ")"
       | (IR.Z_mul_split lg2s @@@ args) =>
         special_name "mulx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_add_with_get_carry lg2s @@@ args) =>
         special_name "addcarryx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_sub_with_get_borrow lg2s @@@ args) =>
         special_name "subborrowx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_zselect ty @@@ args) =>
         special_name_ty "cmovznz" (int.unsigned_counterpart_of ty) ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_value_barrier ty @@@ args) =>
         special_name_ty "value_barrier" ty ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_static_cast int_t @@@ e) =>
         "(" ++ primitive_type_to_string false prefix IR.type.Z (Some int_t) ++ ") Integer.toUnsignedLong(((Number) (" ++ arith_to_string internal_private prefix e ++ ")).intValue())"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string internal_private prefix a ++ ", " ++ arith_to_string internal_private prefix b
       | (IR.Addr @@@ IR.Var _ v) => "error_cannot_take_reference_in_Java_to_" ++ v
       | (IR.Z_add_modulo @@@ (x1, x2, x3)) => "int _error = error_addmodulo"
       | (IR.List_nth _ @@@ _)
       | (IR.Addr @@@ _)
       | (IR.Z_add @@@ _)
       | (IR.Z_mul @@@ _)
       | (IR.Z_sub @@@ _)
       | (IR.Z_land @@@ _)
       | (IR.Z_lor @@@ _)
       | (IR.Z_lxor @@@ _)
       | (IR.Z_add_modulo @@@ _) => "int _error = error_bad_arg"
       | IR.TT => "error_tt"
       end%string%Cexpr.

  (** In Java, there is no munging of return arguments (they remain
      passed by pointers), so all variables are live *)
  Local Instance : IR.OfPHOAS.consider_retargs_live_opt := fun _ _ _ => true.
  Local Instance : IR.OfPHOAS.rename_dead_opt := fun s => s.
  (** No need to lift declarations to the top *)
  Local Instance : IR.OfPHOAS.lift_declarations_opt := false.

  Definition stmt_to_string
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (prefix : string)
             (e : IR.stmt)
    : string :=
    match e with
    | IR.Call val => arith_to_string internal_private prefix val ++ ";"
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      primitive_type_to_string false prefix t sz ++ " " ++ name ++ " = " ++ arith_to_string internal_private prefix val ++ ";"
    | IR.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string internal_private prefix val ++ ";" *)
      "error_trying_to_assign_value_to_non_mutable_variable;"
    | IR.AssignZPtr name sz val =>
      name ++ ".set(" ++ arith_to_string internal_private prefix val ++ ");"
    | IR.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type *)
      primitive_type_to_string true prefix IR.type.Zptr sz ++ " " ++ name ++ " = new " ++ primitive_type_to_string true prefix IR.type.Zptr sz ++ "((" ++ primitive_type_to_string false prefix IR.type.Z sz ++ ")0);"
    | IR.Comment lines _ =>
      String.concat String.NewLine (comment_block (ToString.preprocess_comment_block lines))
    | IR.AssignNth name n val =>
      name ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "] = " ++ arith_to_string internal_private prefix val ++ ";"
    end.

  Definition to_strings
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (prefix : string)
             (e : IR.expr)
    : list string :=
    List.map (stmt_to_string internal_private prefix) e.

  Import Rewriter.Language.Language.Compilers Crypto.Language.API.Compilers IR.OfPHOAS.
  Local Notation tZ := (base.type.type_base base.type.Z).

  Inductive Mode := In | Out.


  (* This would have been nice, but coercions don't work *)
  (* Module Base := Rewriter.Language.Language.Compilers.base. *)

  Fixpoint to_base_arg_list (prefix : string) (mode : Mode) {t} : ToString.OfPHOAS.base_var_data t -> list string :=
    match t return base_var_data t -> _ with
    | tZ =>
      let typ := match mode with In => IR.type.Z | Out => IR.type.Zptr end in
      fun '(n, is_ptr, r, typedef) => [primitive_type_to_string false prefix typ r ++ " " ++ n]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list prefix mode va ++ to_base_arg_list prefix mode vb)%list
    | base.type.list tZ =>
      fun '(n, r, len, typedef) =>
        match mode with
        | In => (* arrays for inputs are immutable borrows *)
          [("final " ++ primitive_type_to_string false prefix IR.type.Z r)
             ++ "[] " (* ++ Decimal.Z.to_string (Z.of_nat len) ++ "] "*)
             ++ n]
        | Out => (* arrays for outputs are mutable borrows *)
          [(primitive_type_to_string false prefix IR.type.Z r)
             ++ "[] " (* ++ Decimal.Z.to_string (Z.of_nat len) ++ "] "*)
             ++ n]
        end
    | base.type.list _ => fun _ => ["error_complex_list"]
    | base.type.option _ => fun _ => ["error_option"]
    | base.type.unit => fun _ => ["error_unit"]
    | base.type.type_base t => fun _ => ["error_" ++ show t]%string
    end%string.

  Definition to_arg_list (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list prefix mode
    | type.arrow _ _ => fun _ => ["error_arrow"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list prefix In x ++ @to_arg_list_for_each_lhs_of_arrow prefix d xs
       end%list.

  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  Definition Java_bin_op_natural_output
    : IR.Z_binop -> ToString.int.type * ToString.int.type -> ToString.int.type
    := fun idc '(t1, t2)
       => ToString.int.union t1 t2.

  (* Does the binary operation commute with (-- mod 2^bw)? *)
  Definition bin_op_commutes_with_mod_pow2 (idc : IR.Z_binop)
    := match idc with
       | IR.Z_land
       | IR.Z_lor
       | IR.Z_lxor
       | IR.Z_add
       | IR.Z_mul
       | IR.Z_sub
         => true
       end.

  Definition Java_bin_op_casts
    : IR.Z_binop -> option ToString.int.type -> ToString.int.type * ToString.int.type -> option ToString.int.type * (option ToString.int.type * option ToString.int.type)
    := fun idc desired_type '(t1, t2)
       => match desired_type with
          | Some desired_type
            => let ct := ToString.int.union t1 t2 in
               if bin_op_commutes_with_mod_pow2 idc
               then
                 (* these operations commute with mod, so we just pre-cast them *)
                 (None, (Some desired_type, Some desired_type))
               else
                 let desired_type' := Some (ToString.int.union ct desired_type) in
                 (desired_type',
                  (get_Zcast_up_if_needed desired_type' (Some t1),
                   get_Zcast_up_if_needed desired_type' (Some t2)))
          | None => (None, (None, None))
          end.

  Definition Java_un_op_casts
    : IR.Z_unop -> option ToString.int.type -> ToString.int.type -> option ToString.int.type * option ToString.int.type
    := fun idc desired_type t
       => match idc with
          | IR.Z_shiftr offset
            => (** N.B. We must cast the expression up to a large
                   enough type to fit 2^offset (importantly, not just
                   2^offset-1), because C considers it to be undefined
                   behavior to shift >= width of the type.  We should
                   probably figure out how to not generate these
                   things in the first place...

                   N.B. We must preserve signedness of the value being
                   shifted, because shift does not commute with
                   mod. *)
            let t' := ToString.int.union_zrange r[0~>2^offset]%zrange t in
            ((** We cast the result down to the specified type, if needed *)
              get_Zcast_down_if_needed desired_type (Some t'),
              (** We cast the argument up to a large enough type *)
              get_Zcast_up_if_needed (Some t') (Some t))
          | IR.Z_shiftl offset
            => (** N.B. We must cast the expression up to a large
                   enough type to fit 2^offset (importantly, not just
                   2^offset-1), because C considers it to be undefined
                   behavior to shift >= width of the type.  We should
                   probably figure out how to not generate these
                   things in the first place...

                   N.B. We make sure that we only left-shift unsigned
                   values, since shifting into the sign bit is
                   undefined behavior. *)
            let rpre_out := match desired_type with
                            | Some rout => Some (ToString.int.union_zrange r[0~>2^offset] (ToString.int.unsigned_counterpart_of rout))
                            | None => Some (ToString.int.of_zrange_relaxed r[0~>2^offset]%zrange)
                            end in
            ((** We cast the result down to the specified type, if needed *)
              get_Zcast_down_if_needed desired_type rpre_out,
              (** We cast the argument up to a large enough type *)
              get_Zcast_up_if_needed rpre_out (Some t))
          | IR.Z_lnot ty
            => ((* if the result is too big, we cast it down; we
                       don't need to upcast it because it'll get
                       picked up by implicit casts if necessary *)
              get_Zcast_down_if_needed desired_type (Some ty),
              (** always cast to the width of the type, unless we are already exactly that type (which the machinery in IR handles *)
              Some ty)
          | IR.Z_value_barrier ty
            => ((* if the result is too big, we cast it down; we
                       don't need to upcast it because it'll get
                       picked up by implicit casts if necessary *)
              get_Zcast_down_if_needed desired_type (Some ty),
              (** always cast to the width of the type, unless we are already exactly that type (which the machinery in IR handles *)
              Some ty)
          | IR.Z_bneg
            => ((* bneg is !, i.e., takes the argument to 1 if its not zero, and to zero if it is zero; so we don't ever need to cast *)
              None, None)
          end.

  Local Instance JavaLanguageCasts : LanguageCasts :=
    {| bin_op_natural_output := Java_bin_op_natural_output
       ; bin_op_casts := Java_bin_op_casts
       ; un_op_casts := Java_un_op_casts
       ; upcast_on_assignment := true
       ; upcast_on_funcall := true
       ; explicit_pointer_variables := true (* Java can't take the address of a variable, so we declare explicit pointer variables *)
    |}.

  Definition to_function_lines
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (internal : bool) (inline : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    (((if internal then "" else "public ") ++ "static void " ++ name)
       ++ "(" ++ String.concat ", " (to_arg_list prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow prefix args) ++
       ") {")%string :: (List.map (fun s => "  " ++ s)%string (to_strings internal_private prefix body)) ++ ["}"%string]%list.

  Definition javadoc_replace (s : string) : string
    := String.replace "<" "&lt;" (String.replace ">" "&gt;" s).

  Definition javadoc_format (ls : list string) : list string
    := ["/**"%string]
         ++ List.map (fun s => s ++ " <p>")%string ls
         ++ [" */"%string].

  Definition ToFunctionLines
             {absint_opts : AbstractInterpretation.Options}
             {relax_zrange : relax_zrange_opt}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z)
             (do_bounds_check : bool) (internal_private : bool) (internal : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
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
      inl ((javadoc_format
              ((List.map (fun s => if (String.length s =? 0)%nat then " *" else (" * " ++ javadoc_replace s))%string (comment indata outdata))
                 ++ match input_bounds_to_string indata inbounds with
                    | nil => nil
                    | ls => [" * Input Bounds:"] ++ List.map (fun v => " *   " ++ javadoc_replace v)%string ls
                    end
                 ++ match bound_to_string outdata outbounds with
                    | nil => nil
                    | ls => [" * Output Bounds:"] ++ List.map (fun v => " *   " ++ javadoc_replace v)%string ls
                    end)
              ++ to_function_lines internal_private internal inline prefix name (indata, outdata, f))%list%string,
           IR.ident_infos.collect_all_infos f intypedefs outtypedefs)
    | inr nil =>
      inr ("Unknown internal error in converting " ++ name ++ " to Java")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to Java:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to Java:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputJavaAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := comment_block;
       ToString.comment_file_header_block := comment_block;
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := @header;
       ToString.footer := @footer;
       ToString.strip_special_infos machine_wordsize infos := infos |}.

End Java.
