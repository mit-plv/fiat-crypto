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

Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Import IR.Compilers.ToString.
Import Stringification.Language.Compilers.
Import Stringification.Language.Compilers.Options.
Import Stringification.Language.Compilers.ToString.
Import Stringification.Language.Compilers.ToString.int.Notations.

Module Rust.
  Definition comment_module_header_block := List.map (fun line => "//! " ++ line)%string.
  Definition comment_block := List.map (fun line => "/** " ++ line ++ " */")%string.


  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [8; 16; 32; 64; 128].
  Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).


  Definition int_type_to_string_opt_typedef {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (private : bool) (all_private : bool) (prefix : string) (t : ToString.int.type) (typedef : option string) : string :=
    int.to_string_gen_opt_typedef stdint_bitwidths "u" "i" "" "" private all_private prefix t typedef.
  Definition int_type_to_string {language_naming_conventions : language_naming_conventions_opt} (private : bool) (prefix : string) (t : ToString.int.type) : string :=
    int_type_to_string_opt_typedef (skip_typedefs:=true) private private prefix t None.

  Definition make_typedef
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             (prefix : string) (internal_private : bool) (private : bool)
             (typedef : typedef_info)
    : list string
    := let '(name, (ty, array_len), description) := name_and_type_and_describe_typedef prefix private typedef in
       ((comment_block description)
          ++ [
                let ty_string := match ty with
                                 | Some ty => int_type_to_string internal_private prefix ty
                                 | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
                                 end in
                let visibility := (if private then "" else "pub ") in
                match array_len with
                | None (* just an integer *) => visibility ++ "type " ++ name ++ " = " ++ ty_string ++ ";"
                | Some None (* unknown array length *) => visibility ++ "type " ++ name ++ " = *mut " ++ ty_string ++ ";"
                | Some (Some len) => "#[derive(Clone, Copy)]" ++ String.NewLine
                  ++ visibility ++ "struct " ++ name ++ "(pub [" ++ ty_string ++ "; " ++ Decimal.Z.to_string (Z.of_nat len) ++ "]);" ++ String.NewLine ++ String.NewLine
                  ++ "impl core::ops::Index<usize> for " ++ name ++ " {" ++ String.NewLine
                  ++ "    type Output = " ++ ty_string ++ ";" ++ String.NewLine
                  ++ "    #[inline]" ++ String.NewLine
                  ++ "    fn index(&self, index: usize) -> &Self::Output {" ++ String.NewLine
                  ++ "        &self.0[index]" ++ String.NewLine
                  ++ "    }" ++ String.NewLine
                  ++ "}" ++ String.NewLine ++ String.NewLine
                  ++ "impl core::ops::IndexMut<usize> for " ++ name ++ " {" ++ String.NewLine
                  ++ "    #[inline]" ++ String.NewLine
                  ++ "    fn index_mut(&mut self, index: usize) -> &mut Self::Output {" ++ String.NewLine
                  ++ "        &mut self.0[index]" ++ String.NewLine
                  ++ "    }" ++ String.NewLine
                  ++ "}"
                end
                ]%string)%list.

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
    := let bitwidths_used := ToString.bitwidths_used infos in
       let type_prefix := (if internal_private then "type " else "pub type ")%string in
       (["";
        "#![allow(unused_parens)]";
        "#![allow(non_camel_case_types)]";
        ""]%string
           ++ (List.flat_map
                 (fun bw
                  => (if IntSet.mem (int.of_bitwidth false bw) bitwidths_used || IntSet.mem (int.of_bitwidth true bw) bitwidths_used
                      then [type_prefix ++ int_type_to_string internal_private prefix (int.of_bitwidth false bw) ++ " = u8;"; (* C: typedef unsigned char prefix_uint1 *)
                           type_prefix ++ int_type_to_string internal_private prefix (int.of_bitwidth true bw) ++ " = i8;" ]%string (* C: typedef signed char prefix_int1 *)
                      else []))
                 [1; 2])
           ++ (if skip_typedefs
               then []
               else List.flat_map
                      (fun td_name =>
                         match List.find (fun '(name, _, _, _) => (td_name =? name)%string) typedef_map with
                         | Some td_info => [""] ++ make_typedef prefix internal_private private td_info
                         | None => ["#error ""Could not find typedef info for '" ++ td_name ++ "'"";"]%string
                         end%list)
                      (typedefs_used infos))
           ++ [""])%list%string.

  (* Instead of "macros for minimum-width integer constants" we tried to
     use numeric casts in Rust. It turns out that it wasn't needed and Rust
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

  Definition primitive_type_to_string_opt_typedef
             {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt}
             (private : bool) (all_private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) (typedef : option string) : string :=
    match t with
    | IR.type.Zptr => "&mut "
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string_opt_typedef private all_private prefix int_t typedef
           | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
           end.
  Definition primitive_type_to_string {language_naming_conventions : language_naming_conventions_opt} (private : bool) (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    primitive_type_to_string_opt_typedef (skip_typedefs:=true) private private prefix t r None.
  Definition primitive_array_type_to_string
             {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt}
             (internal_private : bool) (all_private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) (len : nat) (typedef : option string) : string :=
    match (if skip_typedefs then None else typedef) with
    | Some typedef => format_typedef_name prefix all_private typedef
    | None => "[" ++ primitive_type_to_string internal_private prefix t r ++ "; " ++ Decimal.Z.to_string (Z.of_nat len) ++ "]"
    end.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t, cast_literal prefix (ToString.int.of_zrange_relaxed r[v ~> v]) with
    | IR.type.Z, Some cast => "(" ++ HexString.of_Z v ++ cast ++ ")"
    | IR.type.Z, None => (* just print hex value, no cast *) HexString.of_Z v
    | IR.type.Zptr, _ => "#error ""literal address " ++ HexString.of_Z v ++ """;"
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
       | (IR.Addr @@@ IR.Var _ v) => "&mut " ++ v (* borrow a mutable ref to v *)
       | (IR.Dereference @@@ e) => "( *" ++ arith_to_string internal_private prefix e ++ " )"
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
       | (IR.Z_lnot _ @@@ e) => "(!" ++ arith_to_string internal_private prefix e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " + " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_mul @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " * " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_sub @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " - " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_bneg @@@ e) => "(!" ++ arith_to_string internal_private prefix e ++ ")" (* logical negation. XXX this has different semantics for numbers <>
                                                                        0 or 1 than it did before *)
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
         "(" ++ arith_to_string internal_private prefix e ++ " as " ++ primitive_type_to_string internal_private prefix IR.type.Z (Some int_t) ++ ")"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string internal_private prefix a ++ ", " ++ arith_to_string internal_private prefix b
       | (IR.Z_add_modulo @@@ (x1, x2, x3)) => "#error addmodulo;"
       | (IR.List_nth _ @@@ _)
       | (IR.Addr @@@ _)
       | (IR.Z_add @@@ _)
       | (IR.Z_mul @@@ _)
       | (IR.Z_sub @@@ _)
       | (IR.Z_land @@@ _)
       | (IR.Z_lor @@@ _)
       | (IR.Z_lxor @@@ _)
       | (IR.Z_add_modulo @@@ _) => "#error bad_arg;"
       | IR.TT => "#error tt;"
       end%string%Cexpr.

  Definition stmt_to_string
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (prefix : string) (e : IR.stmt) : string :=
    match e with
    | IR.Call val => arith_to_string internal_private prefix val ++ ";"
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      "let " ++ name ++ ": " ++ primitive_type_to_string internal_private prefix t sz ++ " = " ++ arith_to_string internal_private prefix val ++ ";"
    | IR.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string internal_private prefix val ++ ";" *)
      "#error trying to assign value to non-mutable variable;"
    | IR.AssignZPtr name sz val =>
      "*" ++ name ++ " = " ++ arith_to_string internal_private prefix val ++ ";"
    | IR.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type *)
      "let mut " ++ name ++ ": " ++ primitive_type_to_string internal_private prefix t sz ++ " = 0;"
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


  (* This would have been nice, but coercions don't work *)
  (* Module Base := Rewriter.Language.Language.Compilers.base. *)

  Fixpoint to_base_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) (mode : Mode) {t} : ToString.OfPHOAS.base_var_data t -> list string :=
    match t return base_var_data t -> _ with
    | tZ =>
      let typ := match mode with In => IR.type.Z | Out => IR.type.Zptr end in
      fun '(n, is_ptr, r, typedef) => [n ++ ": " ++ primitive_type_to_string_opt_typedef internal_private all_private prefix typ r typedef]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list internal_private all_private prefix mode va ++ to_base_arg_list internal_private all_private prefix mode vb)%list
    | base.type.list tZ =>
      fun '(n, r, len, typedef) =>
        let modifier := match mode with
                        | In => (* arrays for inputs are immutable borrows *) "&"
                        | Out => (* arrays for outputs are mutable borrows *) "&mut "
                        end in
        [n ++ ": " ++ modifier ++ primitive_array_type_to_string internal_private all_private prefix IR.type.Z r len typedef]
    | base.type.list _ => fun _ => ["#error ""complex list"";"]
    | base.type.option _ => fun _ => ["#error option;"]
    | base.type.unit => fun _ => ["#error unit;"]
    | base.type.type_base t => fun _ => ["#error " ++ show t ++ ";"]%string
    end%string.

  Definition to_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list internal_private all_private prefix mode
    | type.arrow _ _ => fun _ => ["#error arrow;"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list internal_private all_private prefix In x ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix xs
       end%list.

  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  Definition Rust_bin_op_natural_output
    : IR.Z_binop -> ToString.int.type * ToString.int.type -> ToString.int.type
    := fun idc '(t1, t2)
       => ToString.int.union t1 t2.

  Definition Rust_bin_op_casts
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

  Definition Rust_un_op_casts
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

  Local Instance RustLanguageCasts : LanguageCasts :=
    {| bin_op_natural_output := Rust_bin_op_natural_output
       ; bin_op_casts := Rust_bin_op_casts
       ; un_op_casts := Rust_un_op_casts
       ; upcast_on_assignment := true
       ; upcast_on_funcall := true
       ; explicit_pointer_variables := false
    |}.

  Definition to_function_lines {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (private : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    ((if inline then "#[inline]" ++ String.NewLine else "") ++ (if private then "fn " else "pub fn ") ++ name ++
      "(" ++ String.concat ", " (to_arg_list internal_private all_private prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix args) ++
      ") {")%string :: (List.map (fun s => "  " ++ s)%string (to_strings internal_private prefix body)) ++ ["}"%string]%list.

  (** In Rust, there is no munging of return arguments (they remain
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
      inr ("Unknown internal error in converting " ++ name ++ " to Rust")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to Rust:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputRustAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := comment_block;
       ToString.comment_file_header_block := comment_module_header_block;
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := @header;
       ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];
       (** No special handling for any functions *)
       ToString.strip_special_infos machine_wordsize infos := infos |}.

End Rust.
