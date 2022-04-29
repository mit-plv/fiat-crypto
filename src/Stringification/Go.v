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

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope zrange_scope.
Local Open Scope Z_scope.

Import IR.Compilers.ToString.
Import Stringification.Language.Compilers.
Import Stringification.Language.Compilers.Options.
Import Stringification.Language.Compilers.ToString.
Import Stringification.Language.Compilers.ToString.int.Notations.

Module Go.

  Definition comment_block (lines : list string) : list string
    := match lines with
       | [] => []
       | [""] => [""]
       | [line] => ["// " ++ line]%string
       | lines => List.map (fun s => if (String.length s =? 0)%nat then "//" else "// " ++ s)%string lines
       end%list%string.

  Definition comment_block_extra_newlines (lines : list string) : list string
    := match lines with
       | [] => []
       | [""] => [""]
       | [line] => ["// " ++ line]%string
       | lines => List.tl (List.flat_map (fun s => ["//";
                                                   if (String.length s =? 0)%nat
                                                   then "//"
                                                   else "// " ++ s])%string lines)
       end%list%string.

  (* Supported integer bitwidths *)
  Definition stdint_bitwidths : list Z := [8; 16; 32; 64].
  (* supported bitwidth for things like bits.Mul64 *)
  Definition bits_std_bitwidths : list Z := [32; 64].
  Definition is_bits_standard_bitwidth (bw : Z) := existsb (Z.eqb bw) bits_std_bitwidths.
  Definition is_standard_bitwidth (bw : Z) := existsb (Z.eqb bw) stdint_bitwidths.
  Definition is_special_bitwidth (bw : Z) := negb (is_standard_bitwidth bw).
  Definition is_nonbits_special_bitwidth (bw : Z) := negb (is_bits_standard_bitwidth bw).

  Definition int_type_to_string_opt_typedef {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (private : bool) (all_private : bool) (prefix : string) (t : ToString.int.type) (typedef : option string) : string :=
    int.to_string_gen_opt_typedef stdint_bitwidths "uint" "int" "" "" private all_private prefix t typedef.
  Definition int_type_to_string {language_naming_conventions : language_naming_conventions_opt} (private : bool) (prefix : string) (t : ToString.int.type) : string :=
    int_type_to_string_opt_typedef (skip_typedefs:=true) private private prefix t None.

  Definition make_typedef
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             (prefix : string) (internal_private : bool) (private : bool)
             (typedef : typedef_info)
    : list string
    := let '(name, (ty, array_len), description) := name_and_type_and_describe_typedef prefix private typedef in
       ((comment_block_extra_newlines description)
          ++ ["type "
                ++ name ++ " " ++
                match array_len with
                | None (* just an integer *) => ""
                | Some None (* unknown array length *) => "[]"
                | Some (Some len) => "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]"
                end
                ++ match ty with
                   | Some ty => int_type_to_string internal_private prefix ty
                   | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
                   end]%string)%list.

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
       let needs_bits_import (* we only need the bits import if we use addcarryx/subborrowx/mulx with a standard bitwidth *)
           := PositiveSet.exists_
                (fun bw => is_bits_standard_bitwidth (Z.pos bw))
                (PositiveSet.union (ToString.addcarryx_lg_splits infos)
                                   (ToString.mulx_lg_splits infos)) in
       let type_prefix := "type "%string in
       let special_addcarryx_lg_splits
           := List.filter
                (fun bw => negb (List.existsb (Z.eqb bw) relax_adc_sbb_return_carry_to_bitwidth))
                (List.filter
                   is_bits_standard_bitwidth
                   (List.map
                      Z.pos
                      (PositiveSet.elements (ToString.addcarryx_lg_splits infos)))) in
       let carry_type := (if IntSet.mem _Bool bitwidths_used || IntSet.mem (ToString.int.signed_counterpart_of _Bool) bitwidths_used
                          then int_type_to_string internal_private prefix _Bool
                          else if IntSet.mem uint8 bitwidths_used || IntSet.mem int8 bitwidths_used
                               then int_type_to_string internal_private prefix uint8
                               else int_type_to_string internal_private prefix (int.of_bitwidth false(*unsigned*) machine_wordsize)) in
       strip_trailing_newlines
         (((if newline_before_package_declaration then [""] else [])
             ++ ["package " ++ package_name prefix;
                ""]%string)
            ++ (if needs_bits_import then ["import ""math/bits"""; ""]%string else [])
            ++ (let typedefs
                    := let carry_bitwidth := 64 (* c.f. https://github.com/mit-plv/fiat-crypto/pull/1006#issuecomment-892625927 *) in
                       let carry_typedef_comment := (" // We use uint" ++ Decimal.Z.to_string carry_bitwidth ++ " instead of a more narrow type for performance reasons; see https://github.com/mit-plv/fiat-crypto/pull/1006#issuecomment-892625927")%string in
                       List.flat_map
                         (fun bw
                          => (if IntSet.mem (int.of_bitwidth false bw) bitwidths_used || IntSet.mem (int.of_bitwidth true bw) bitwidths_used
                              then [type_prefix ++ int_type_to_string internal_private prefix (int.of_bitwidth false bw) ++ " uint" ++ Decimal.Z.to_string carry_bitwidth ++ carry_typedef_comment;
                                   type_prefix ++ int_type_to_string internal_private prefix (int.of_bitwidth true bw) ++ " int" ++ Decimal.Z.to_string carry_bitwidth ++ carry_typedef_comment]%string
                              else []))
                         [1; 2] in
                let typedefs :=
                    typedefs
                      ++ if skip_typedefs
                         then []
                         else List.flat_map
                                (fun td_name =>
                                   match List.find (fun '(name, _, _, _) => (td_name =? name)%string) typedef_map with
                                   | Some td_info => [""] ++ make_typedef prefix internal_private private td_info
                                   | None => ["var _ = error_Go_Could_not_find_typedef_info_for_" ++ td_name]%string
                                   end%list)
                                (typedefs_used infos) in
                match typedefs with
                | [] => []
                | _::_ => typedefs ++ [""]
                end)
            ++ (if IntSet.mem uint128 bitwidths_used || IntSet.mem int128 bitwidths_used
                then ["var _ = error_Go_output_does_not_support_128_bit_integers___instead_use_rewriting_rules_for_removing_128_bit_integers"]%string
                else [])
            ++ (List.tl
                  (List.flat_map
                     (fun bw
                      => let s_bw := Decimal.Z.to_string bw in
                         List.flat_map
                           (fun '(newname, bitsname)
                            => [""%string]
                                 ++ (comment_block
                                       [text_before_function_name ++ newname ++ " is a thin wrapper around " ++ bitsname ++ " that uses " ++ carry_type ++ " rather than uint" ++ s_bw]%string)
                                 ++ ["func " ++ newname ++ "(x uint" ++ s_bw ++ ", y uint" ++ s_bw ++ ", carry " ++ carry_type ++ ") (uint" ++ s_bw ++ ", " ++ carry_type ++ ") {"
                                     ; String.Tab ++ "sum, carryOut := " ++ bitsname ++ "(x, y, uint" ++ s_bw ++ "(carry))"
                                     ; String.Tab ++ "return sum, " ++ carry_type ++ "(carryOut)"
                                     ; "}"]%string)
                           [(ToString.format_special_function_name internal_private prefix "addcarryx" false(*unsigned*) bw, "bits.Add" ++ s_bw)
                            ; (ToString.format_special_function_name internal_private prefix "subborrowx" false(*unsigned*) bw, "bits.Sub" ++ s_bw)]%string)
                     special_addcarryx_lg_splits)))%list.

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

  Definition primitive_type_to_string_opt_typedef
             {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt}
             (private : bool) (all_private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) (typedef : option string) : string :=
    match t with
    | IR.type.Zptr => "*"
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string_opt_typedef private all_private prefix int_t typedef
           | None => "ℤ" (* blackboard bold Z for unbounded integers (which don't actually exist, and thus will error) *)
           end.
  Definition primitive_type_to_string
             {language_naming_conventions : language_naming_conventions_opt} (private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    primitive_type_to_string_opt_typedef (skip_typedefs:=true) private private prefix t r None.
  Definition primitive_array_type_to_string
             {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt}
             (internal_private : bool) (all_private : bool)
             (prefix : string) (t : IR.type.primitive)
             (r : option ToString.int.type) (len : nat) (typedef : option string) : string :=
    match (if skip_typedefs then None else typedef) with
    | Some typedef => format_typedef_name prefix all_private typedef
    | None => "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]" ++
                  primitive_type_to_string internal_private prefix t r
    end.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t, cast_literal prefix (ToString.int.of_zrange_relaxed r[v ~> v]) with
    | IR.type.Z, Some cast => "(" ++ HexString.of_Z v ++ cast ++ ")"
    | IR.type.Z, None => (* just print hex value, no cast *) HexString.of_Z v
    | IR.type.Zptr, _ => "var _error = literal_address_" ++ HexString.of_Z v
    end.

  Import IR.Notations.

  Fixpoint arith_to_string
           {language_naming_conventions : language_naming_conventions_opt}
           {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
           (internal_private : bool) (prefix : string)
           {t} (e : IR.arith_expr t)
    : string
    := let special_name_ty name ty := ToString.format_special_function_name_ty internal_private prefix name ty in
       let special_name name bw := ToString.format_special_function_name internal_private prefix name false(*unsigned*) bw in
       match e with
       (* integer literals *)
       | (IR.literal v @@@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@@ IR.Var _ v) => v ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "]"
       (* (de)referencing *)
       | (IR.Addr @@@ IR.Var _ v) => "&" ++ v
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
       | (IR.Z_lnot _ @@@ e) => "(^" ++ arith_to_string internal_private prefix e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " + " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_mul @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " * " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_sub @@@ (x1, x2)) =>
         "(" ++ arith_to_string internal_private prefix x1 ++ " - " ++ arith_to_string internal_private prefix x2 ++ ")"
       | (IR.Z_bneg @@@ e) => "(!/* TODO: FIX ME */ " ++ arith_to_string internal_private prefix e ++ ")"
       | (IR.Z_mul_split lg2s @@@ args) =>
         match is_bits_standard_bitwidth lg2s, args with
         | true, ((IR.Addr @@@ lo, IR.Addr @@@ hi), args)
           => (arith_to_string internal_private prefix hi ++ ", " ++ arith_to_string internal_private prefix lo)
                ++ " = bits.Mul"
                ++ Decimal.Z.to_string lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
         | _, _
           => special_name "mulx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
         end
       | (IR.Z_add_with_get_carry lg2s @@@ args) =>
         let (func_name, wrap_carry)
             := (if List.existsb (Z.eqb lg2s) relax_adc_sbb_return_carry_to_bitwidth
                 then ("bits.Add" ++ Decimal.Z.to_string lg2s, fun c => "uint" ++ Decimal.Z.to_string lg2s ++ "(" ++ c ++ ")")
                 else (special_name "addcarryx" lg2s, fun c => c))%core in
         match is_bits_standard_bitwidth lg2s, args with
         | true, ((IR.Addr @@@ v, IR.Addr @@@ c), (cin, x, y))
           => (arith_to_string internal_private prefix v ++ ", " ++ arith_to_string internal_private prefix c)
                ++ " = " ++ func_name
                ++ "(" ++ arith_to_string internal_private prefix x ++ ", " ++ arith_to_string internal_private prefix y ++ ", " ++ wrap_carry (arith_to_string internal_private prefix cin) ++ ")"
         | _, _
           => special_name "addcarryx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
         end
       | (IR.Z_sub_with_get_borrow lg2s @@@ args) =>
         let (func_name, wrap_carry)
             := (if List.existsb (Z.eqb lg2s) relax_adc_sbb_return_carry_to_bitwidth
                 then ("bits.Sub" ++ Decimal.Z.to_string lg2s, fun c => "uint" ++ Decimal.Z.to_string lg2s ++ "(" ++ c ++ ")")
                 else (special_name "subborrowx" lg2s, fun c => c))%core in
         match is_bits_standard_bitwidth lg2s, args with
         | true, ((IR.Addr @@@ v, IR.Addr @@@ b), (bin, x, y))
           => (arith_to_string internal_private prefix v ++ ", " ++ arith_to_string internal_private prefix b)
                ++ " = " ++ func_name
                ++ "(" ++ arith_to_string internal_private prefix x ++ ", " ++ arith_to_string internal_private prefix y ++ ", " ++ wrap_carry (arith_to_string internal_private prefix bin) ++ ")"
         | _, _
           => special_name "subborrowx" lg2s ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
         end
       | (IR.Z_value_barrier ty @@@ args) =>
         special_name_ty "value_barrier" ty ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_zselect ty @@@ args) =>
         special_name_ty "cmovznz" ty ++ "(" ++ arith_to_string internal_private prefix args ++ ")"
       | (IR.Z_static_cast int_t @@@ e) =>
         primitive_type_to_string internal_private prefix IR.type.Z (Some int_t) ++ "(" ++ arith_to_string internal_private prefix e ++ ")"
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string internal_private prefix a ++ ", " ++ arith_to_string internal_private prefix b
       | (IR.Z_add_modulo @@@ (x1, x2, x3)) => "var _error = error_addmodulo"
       | (IR.List_nth _ @@@ _)
       | (IR.Addr @@@ _)
       | (IR.Z_add @@@ _)
       | (IR.Z_mul @@@ _)
       | (IR.Z_sub @@@ _)
       | (IR.Z_land @@@ _)
       | (IR.Z_lor @@@ _)
       | (IR.Z_lxor @@@ _)
       | (IR.Z_add_modulo @@@ _) => "var _error = error_bad_arg"
       | IR.TT => "var _error = error_tt"
       end%string%Cexpr.

  (** In Go, we munge return arguments of some functions above, so
      there is the possibility for them to become unused *)
  Local Instance : IR.OfPHOAS.consider_retargs_live_opt
    := fun _ _ idc
       => match idc with
          | IR.Z_mul_split lg2s
          | IR.Z_add_with_get_carry lg2s
          | IR.Z_sub_with_get_borrow lg2s
            (* these are munged; having a variable be used as a return
               from these functions doesn't imply that it is live *)
            => is_nonbits_special_bitwidth lg2s
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
  (** No need to lift declarations to the top *)
  Local Instance : IR.OfPHOAS.lift_declarations_opt := false.

  Definition stmt_to_string
             {language_naming_conventions : language_naming_conventions_opt}
             {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
             (internal_private : bool) (prefix : string)
             (e : IR.stmt)
    : string :=
    match e with
    | IR.Call val => arith_to_string internal_private prefix val
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      name ++ " := " ++ arith_to_string internal_private prefix val
    | IR.Assign false _ sz name val =>
    (* This corresponds to assignment to a non-pointer variable and should never ever
       happen in our generated code. Fiat-crypto handles it but I
       haven't found and instance of this to their generated code *)
    (* code : name ++ " = " ++ arith_to_string internal_private prefix val ++ ";" *)
      "var _error = error_trying_to_assign_value_to_non_mutable_variable"
    | IR.AssignZPtr name sz val =>
      "*" ++ name ++ " = " ++ arith_to_string internal_private prefix val
    | IR.DeclareVar t sz name =>
      (* Local uninitialized declarations become mut declarations, and
         are initialized to 0. *)
      (* The assumptions here, based on fiat-crypto code generation
         patterns, are that 1.) this variable will be an argument to a
         call that will store its result in this variable. 2.) this will
         have a non-pointer an integer type *)
      "var " ++ name ++ " " ++ primitive_type_to_string internal_private prefix t sz
    | IR.Comment lines _ =>
      String.concat String.NewLine (comment_block (ToString.preprocess_comment_block lines))
    | IR.AssignNth name n val =>
      name ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "] = " ++ arith_to_string internal_private prefix val
    end.

  Definition to_strings
             {language_naming_conventions : language_naming_conventions_opt}
             {relax_adc_sbb_return_carry_to_bitwidth : relax_adc_sbb_return_carry_to_bitwidth_opt}
             (internal_private : bool) (prefix : string)
             (e : IR.expr)
    : list string :=
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
      fun '(n, is_ptr, r, typedef) => [n ++ " " ++ primitive_type_to_string_opt_typedef internal_private all_private prefix typ r typedef]
    | base.type.prod A B =>
      fun '(va, vb) => (to_base_arg_list internal_private all_private prefix mode va ++ to_base_arg_list internal_private all_private prefix mode vb)%list
    | base.type.list tZ =>
      fun '(n, r, len, typedef) =>
        [ n ++ " *" ++ primitive_array_type_to_string internal_private all_private prefix IR.type.Z r len typedef]
    | base.type.list _ => fun _ => ["var _error = error_complex_list"]
    | base.type.option _ => fun _ => ["var _error = error_option"]
    | base.type.unit => fun _ => ["var _error = error_unit"]
    | base.type.type_base t => fun _ => ["var _error = error_" ++ show t]%string
    end%string.

  Definition to_arg_list {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) (mode : Mode) {t} : var_data t -> list string :=
    match t return var_data t -> _ with
    | type.base t => to_base_arg_list internal_private all_private prefix mode
    | type.arrow _ _ => fun _ => ["var _error = error_arrow"]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow {language_naming_conventions : language_naming_conventions_opt} {skip_typedefs : skip_typedefs_opt} (internal_private : bool) (all_private : bool) (prefix : string) {t} : type.for_each_lhs_of_arrow var_data t -> list string
    := match t return type.for_each_lhs_of_arrow var_data t -> _ with
       | type.base t => fun _ => nil
       | type.arrow s d
         => fun '(x, xs)
            => to_arg_list internal_private all_private prefix In x ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix xs
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
       | IR.Z_lxor
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

  Local Instance GoLanguageCasts : LanguageCasts :=
    {| bin_op_natural_output := Go_bin_op_natural_output
       ; bin_op_casts := Go_bin_op_casts
       ; un_op_casts := Go_un_op_casts
       ; upcast_on_assignment := true
       ; upcast_on_funcall := true
       ; explicit_pointer_variables := false
    |}.

  Definition to_function_lines {language_naming_conventions : language_naming_conventions_opt} {output_options : output_options_opt} (internal_private : bool) (private : bool) (all_private : bool) (inline : bool) (prefix : string) (name : string)
             {t}
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    ((("func "
         ++ name
         ++ "(" ++ String.concat ", " (to_arg_list internal_private all_private prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix args)
         ++ ") {")%string)
       :: (List.map (fun s => String.Tab ++ s)%string (to_strings internal_private prefix body))
       ++ ["}"%string])%list.

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
      inl ((comment_block
              ((comment indata outdata)
                 ++ match input_bounds_to_string indata inbounds with
                    | nil => nil
                    | ls => ["Input Bounds:"] ++ List.map (fun v => "  " ++ v)%string ls
                    end
                 ++ match bound_to_string outdata outbounds with
                    | nil => nil
                    | ls => ["Output Bounds:"] ++ List.map (fun v => "  " ++ v)%string ls
                    end)%list%string
              ++ to_function_lines internal_private private all_private inline prefix name (indata, outdata, f))%list,
           IR.ident_infos.collect_all_infos f intypedefs outtypedefs)
    | inr nil =>
      inr ("Unknown internal error in converting " ++ name ++ " to Go")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to Go:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to Go:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputGoAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block := comment_block;
       ToString.comment_file_header_block := comment_block_extra_newlines;
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := @header;
       ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];
       ToString.strip_special_infos machine_wordsize := strip_special_infos |}.

End Go.
