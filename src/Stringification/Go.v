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
Import Stringification.Language.Compilers.Options.

Module Go.

  (* Header imports and type defs *)
  Definition header (static : bool) (prefix : string) (infos : ToString.ident_infos)
  : list string
    (* N.B. We don't do anything with static; we never export anything *)
    := let bitwidths_used := ToString.bitwidths_used infos in
       let needs_bits_import (* we only need the bits import if we use addcarryx/subborrowx/mulx *)
           := negb ((PositiveSet.is_empty (ToString.addcarryx_lg_splits infos))
                      && (PositiveSet.is_empty (ToString.mulx_lg_splits infos))) in
       let type_prefix := ("type " ++ prefix)%string in
       let pkg_name := if endswith "_" prefix then substring 0 (String.length prefix - 1) prefix else prefix in
       ((["package " ++ pkg_name;
            ""]%string)
          ++ (if needs_bits_import then ["import ""math/bits"""]%string else [])
          ++ (if PositiveSet.mem 1 bitwidths_used
              then [type_prefix ++ "uint1 int"; (* C: typedef unsigned char prefix_uint1 *)
                      type_prefix ++ "int1 int" ]%string (* C: typedef signed char prefix_int1 *)
              else [])
          ++ (if PositiveSet.mem 2 bitwidths_used
              then [type_prefix ++ "uint2 uint8";
                      type_prefix ++ "int2 int8" ]%string
              else [])
          ++ (if PositiveSet.mem 128 bitwidths_used
              then ["var _ = error_Go_output_does_not_support_128_bit_integers___instead_use_rewriting_rules_for_removing_128_bit_integers"]%string
              else []))%list.

  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
  (* supported bitwidth for things like bits.Mul64 *)
  Definition bits_std_bitwidths : list Z := [32; 64].
  Definition is_special_bitwidth (bw : Z) := negb (existsb (Z.eqb bw) stdint_bitwidths).


  Definition int_type_to_string (prefix : string) (t : ToString.int.type) : string :=
    ((if is_special_bitwidth (ToString.int.bitwidth_of t) then prefix else "")
       ++ (if ToString.int.is_unsigned t then "uint" else "int")
       ++ decimal_string_of_Z (ToString.int.bitwidth_of t))%string.


  (* Instead of "macros for minimum-width integer constants" we tried to
     use numeric casts in Go. It turns out that it wasn't needed and Go
     will figure out the types of the litterals, so disabling this for
     now *)
  Definition cast_literal (prefix : string) (t : ToString.int.type) : option string :=
    if Z.ltb (ToString.int.bitwidth_of t) 8
    then None
    else None.


  (* (Comment modified from) Zoe: In fiat-crypto C functions are void
     and as such, they receive pointers to the result as
     argumnets. The C code before calling a function, declares
     uninitializedinteger pointers and passes them as arguments.  In
     Go to do that, we declare an initialized (to 0) mutable, and pass
     a mutable reference to the callee.

     In the longer term, we should examine whether we should use
     non-void functions in Go and just return the result *)

  Definition primitive_type_to_string (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    match t with
    | IR.type.Zptr => "*"
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string prefix int_t
           | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
           end.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t, cast_literal prefix (ToString.int.of_zrange_relaxed r[v ~> v]) with
    | IR.type.Z, Some cast => "(" ++ HexString.of_Z v ++ cast ++ ")"
    | IR.type.Z, None => (* just print hex value, no cast *) HexString.of_Z v
    | IR.type.Zptr, _ => "var _error = literal_address_" ++ HexString.of_Z v
    end.

  Import IR.Notations.

  Fixpoint arith_to_string (prefix : string) {t} (e : IR.arith_expr t) : string
    := match e with
       (* integer literals *)
       | (IR.literal v @@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@ IR.Var _ v) => "(" ++ v ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "])"
       (* (de)referencing *)
       | (IR.Addr @@ IR.Var _ v) => "&" ++ v
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
       | (IR.Z_lnot _ @@ e) => "(^" ++ arith_to_string prefix e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " + " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_mul @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " * " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_sub @@ (x1, x2)) =>
         "(" ++ arith_to_string prefix x1 ++ " - " ++ arith_to_string prefix x2 ++ ")"
       | (IR.Z_bneg @@ e) => "(!/* TODO: FIX ME */ " ++ arith_to_string prefix e ++ ")"
       | (IR.Z_mul_split lg2s @@ args) =>
         match List.existsb (Z.eqb lg2s) bits_std_bitwidths, args with
         | true, ((IR.Addr @@ hi, IR.Addr @@ lo), args)
           => (arith_to_string prefix hi ++ ", " ++ arith_to_string prefix lo)
                ++ " = bits.Mul"
                ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
         | _, _
           => prefix
                ++ "mulx_u"
                ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
         end
       | (IR.Z_add_with_get_carry lg2s @@ args) =>
         match List.existsb (Z.eqb lg2s) bits_std_bitwidths, args with
         | true, ((IR.Addr @@ v, IR.Addr @@ c), (cin, x, y))
           => (arith_to_string prefix v ++ ", " ++ arith_to_string prefix c)
                ++ " = bits.Add"
                ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix x ++ ", " ++ arith_to_string prefix y ++ ", " ++ arith_to_string prefix cin ++ ")"
         | _, _
           => prefix
                ++ "addcarryx_u"
                ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
         end
       | (IR.Z_sub_with_get_borrow lg2s @@ args) =>
         match List.existsb (Z.eqb lg2s) bits_std_bitwidths, args with
         | true, ((IR.Addr @@ v, IR.Addr @@ b), (bin, x, y))
           => (arith_to_string prefix v ++ ", " ++ arith_to_string prefix b)
                ++ " = bits.Sub"
                ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix x ++ ", " ++ arith_to_string prefix y ++ ", " ++ arith_to_string prefix bin ++ ")"
         | _, _
           => prefix
                ++ "subborrowx_u"
                ++ decimal_string_of_Z lg2s ++ "(" ++ arith_to_string prefix args ++ ")"
         end
       | (IR.Z_zselect ty @@ args) =>
         prefix
           ++ "cmovznz_"
           ++ (if ToString.int.is_unsigned ty then "u" else "")
           ++ decimal_string_of_Z (ToString.int.bitwidth_of ty) ++ "(" ++ @arith_to_string prefix _ args ++ ")"
       | (IR.Z_static_cast int_t @@ e) =>
         primitive_type_to_string prefix IR.type.Z (Some int_t) ++ "(" ++ arith_to_string prefix e ++ ")"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string prefix a ++ ", " ++ arith_to_string prefix b
       | (IR.Z_add_modulo @@ (x1, x2, x3)) => "var _error = error_addmodulo"
       | (IR.List_nth _ @@ _)
       | (IR.Addr @@ _)
       | (IR.Z_add @@ _)
       | (IR.Z_mul @@ _)
       | (IR.Z_sub @@ _)
       | (IR.Z_land @@ _)
       | (IR.Z_lor @@ _)
       | (IR.Z_add_modulo @@ _) => "var _error = error_bad_arg"
       | TT => "var _error = error_tt"
       end%string%Cexpr.

  (** In Go, we munge return arguments of some functions above, so
      there is the possibility for them to become unused *)
  Local Instance : IR.OfPHOAS.consider_retargs_live_opt
    := fun _ _ idc
       => match idc with
          | IR.Z_mul_split _
          | IR.Z_add_with_get_carry _
          | IR.Z_sub_with_get_borrow _
            (* these are munged; having a variable be used as a return
               from these functions doesn't imply that it is live *)
            => false
          | IR.literal _
          | IR.List_nth _
          | IR.Addr
          | IR.Dereference
          | IR.iunop _
          | IR.ibinop _
          | IR.Z_zselect _
          | IR.Z_add_modulo
          | IR.Z_static_cast _
            => true (* these are not munged *)
          end.
  (** In Go, assignment to an unused variable can be replaced with assignment to _ *)
  Local Instance : IR.OfPHOAS.rename_dead_opt := fun _ => "_"%string.

  Fixpoint stmt_to_string (prefix : string) (e : IR.stmt) : string :=
    match e with
    | IR.Call val => arith_to_string prefix val
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      "var " ++ name ++ " " ++ primitive_type_to_string prefix t sz ++ " = " ++ arith_to_string prefix val
    | IR.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string prefix val ++ ";" *)
      "var _error = error_trying_to_assign_value_to_non_mutable_variable"
    | IR.AssignZPtr name sz val =>
      "*" ++ name ++ " = " ++ arith_to_string prefix val
    | IR.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type *)
      "var " ++ name ++ " " ++ primitive_type_to_string prefix t sz
    | IR.AssignNth name n val =>
      name ++ "[" ++ decimal_string_of_Z (Z.of_nat n) ++ "] = " ++ arith_to_string prefix val
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
      fun '(n, is_ptr, r) => [n ++ " " ++ primitive_type_to_string prefix typ r]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list prefix mode va ++ to_base_arg_list prefix mode vb)%list
    | base.type.list tZ =>
      fun '(n, r, len) =>
        match mode with
        | In => (* arrays for inputs are immutable borrows *)
          [ n ++ " " ++
              "*[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ++
              primitive_type_to_string prefix IR.type.Z r ]
        | Out => (* arrays for outputs are mutable borrows *)
          [ n ++ " " ++
              "*[" ++ decimal_string_of_Z (Z.of_nat len) ++ "]" ++
              primitive_type_to_string prefix IR.type.Z r ]
        end
    | base.type.list _ => fun _ => ["var _error = error_complex_list"]
    | base.type.option _ => fun _ => ["var _error = error_option"]
    | base.type.unit => fun _ => ["var _error = error_unit"]
    | base.type.type_base t => fun _ => ["var _error = error_" ++ show false t]%string
    end%string.

  Definition to_arg_list (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list prefix mode
    | type.arrow _ _ => fun _ => ["var _error = error_arrow"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list prefix In x ++ @to_arg_list_for_each_lhs_of_arrow prefix d xs
       end%list.

  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  Definition Go_bin_op_natural_output
    : IR.Z_binop -> ToString.int.type * ToString.int.type -> ToString.int.type
    := fun idc '(t1, t2)
       => ToString.int.union t1 t2.

  (* Does the binary operation commute with (-- mod 2^bw)? *)
  Definition bin_op_commutes_with_mod_pow2 (idc : IR.Z_binop)
    := match idc with
       | IR.Z_land
       | IR.Z_lor
       | IR.Z_add
       | IR.Z_mul
       | IR.Z_sub
         => true
       end.

  Definition Go_bin_op_casts
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

  Definition Go_un_op_casts
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
          | Z_bneg
            => ((* bneg is !, i.e., takes the argument to 1 if its not zero, and to zero if it is zero; so we don't ever need to cast *)
              None, None)
          end.

  Local Instance GoLanguageCasts : LanguageCasts :=
    {| bin_op_natural_output := Go_bin_op_natural_output
       ; bin_op_casts := Go_bin_op_casts
       ; un_op_casts := Go_un_op_casts
       ; upcast_on_assignment := true
       ; upcast_on_funcall := true
       ; explicit_pointer_variables := false
    |}.

  Definition to_function_lines (static : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    ("/*inline*/" ++ String.NewLine ++ "func " ++ name ++
      "(" ++ String.concat ", " (to_arg_list prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow prefix args) ++
      ") {")%string :: (List.map (fun s => "  " ++ s)%string (to_strings prefix body)) ++ ["}"%string]%list.

  Definition strip_special_infos (infos : ToString.ident_infos) : ToString.ident_infos
    := ToString.ident_info_diff
         infos
         (List.fold_right
            ToString.ident_info_union
            ToString.ident_info_empty
            (List.flat_map
               (fun bw
                => [IR.ident_infos.collect_infos_of_ident (IR.Z_mul_split bw)
                    ; IR.ident_infos.collect_infos_of_ident (IR.Z_add_with_get_carry bw)
                    ; IR.ident_infos.collect_infos_of_ident (IR.Z_sub_with_get_borrow bw)])
               bits_std_bitwidths)).

  Definition ToFunctionLines
             {relax_zrange : relax_zrange_opt}
             (do_bounds_check : bool) (static : bool) (prefix : string) (name : string)
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
           IR.ident_infos.collect_infos f)
    | inr nil =>
      inr ("Unknown internal error in converting " ++ name ++ " to Go")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to Go:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to Go:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputGoAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := List.map (fun line => "/* " ++ line ++ " */")%string;
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := header;
       ToString.footer := fun _ _ _ => [];
       ToString.strip_special_infos := strip_special_infos |}.

End Go.
