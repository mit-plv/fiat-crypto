From Coq Require Import ZArith MSetPositive FMapPositive
     String Ascii Bool List HexString.
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

  Definition native_split (bw : Z) : bool :=
    (bw =? int.bitwidth_of (int.of_bitwidth false bw))%Z.

  (* Keep carry chains at limb width so Zig can lower them to native
     overflow instructions.  Only multiplication needs a double-width
     intermediate.  The carry output may be widened by the CLI option,
     but the input carry is always a bit. *)
  Definition carry_helpers
             {language_naming_conventions : language_naming_conventions_opt}
             {output_options : output_options_opt}
             (internal_private : bool) (prefix : string) (bw : Z) : list string :=
    let ty := int_type_to_string (int.of_bitwidth false bw) in
    let carry_ty := if List.existsb (Z.eqb bw) relax_adc_sbb_return_carry_to_bitwidth
                    then ty else "u1" in
    List.flat_map
      (fun '(name, op, description) =>
         ["";
          "/// " ++ description;
          (if internal_private then "fn " else "pub fn ") ++
            ToString.format_special_function_name internal_private prefix name false bw ++
            "(out1: *" ++ ty ++ ", out2: *" ++ carry_ty ++ ", arg1: u1, arg2: " ++ ty ++ ", arg3: " ++ ty ++ ") void {";
          "    @setRuntimeSafety(mode == .debug);";
          "";
          "    const x = @" ++ op ++ "WithOverflow(arg2, arg3);";
          "    const y = @" ++ op ++ "WithOverflow(x[0], arg1);";
          "    out1.* = y[0];";
          "    out2.* = x[1] | y[1];";
          "}"]%string)
      [("addcarryx", "add", "Add two limbs and a carry bit, returning the sum modulo 2^" ++ Decimal.Z.to_string bw ++ " and the carry bit.");
       ("subborrowx", "sub", "Subtract two limbs and a borrow bit, returning the difference modulo 2^" ++ Decimal.Z.to_string bw ++ " and the borrow bit.")]%string.

  Definition mul_helper
             {language_naming_conventions : language_naming_conventions_opt}
             (internal_private : bool) (prefix : string) (bw : Z) : list string :=
    let ty := int_type_to_string (int.of_bitwidth false bw) in
    let wide_ty := int_type_to_string (int.of_bitwidth false (2 * bw)) in
    ["";
     "/// Multiply two limbs, returning the low and high halves of the product.";
     (if internal_private then "fn " else "pub fn ") ++
       ToString.format_special_function_name internal_private prefix "mulx" false bw ++
       "(out1: *" ++ ty ++ ", out2: *" ++ ty ++ ", arg1: " ++ ty ++ ", arg2: " ++ ty ++ ") void {";
     "    @setRuntimeSafety(mode == .debug);";
     "";
     "    const x = @as(" ++ wide_ty ++ ", arg1) * arg2;";
     "    out1.* = @truncate(x);";
     "    out2.* = @intCast(x >> " ++ Decimal.Z.to_string bw ++ ");";
     "}"]%string.

  (* Hide the all-zero/all-one range of a selection mask from LLVM.  Without
     this barrier it may replace arithmetic selection with pointer selection
     or masked loads.  Split wide masks so asm operands fit native registers. *)
  Definition selection_mask_helper
             {language_naming_conventions : language_naming_conventions_opt}
             (internal_private : bool) (prefix : string) (t : int.type) : list string :=
    let ty := int_type_to_string t in
    ["";
     "/// Keep selection masks opaque to the optimizer without adding instructions.";
     (if internal_private then "fn " else "pub fn ") ++
       ToString.format_special_function_name_ty internal_private prefix "selection_mask" t ++
       "(arg1: u1) " ++ ty ++ " {";
     "    @setRuntimeSafety(mode == .debug);";
     "";
     "    const value: " ++ ty ++ " = 0 -% " ++
       (if (int.bitwidth_of t =? 1)%Z then "arg1" else "@as(" ++ ty ++ ", arg1)") ++ ";";
     "    if (@inComptime()) return value;";
     "    if (@bitSizeOf(" ++ ty ++ ") <= @bitSizeOf(usize)) {";
     "        return asm (""""";
     "            : [mask] ""=r"" (-> " ++ ty ++ "),";
     "            : [value] ""0"" (value),";
     "        );";
     "    }";
     "    var mask: " ++ ty ++ " = 0;";
     "    inline for (0..@divExact(@bitSizeOf(" ++ ty ++ "), @bitSizeOf(usize))) |i| {";
     "        const shift = i * @bitSizeOf(usize);";
     "        const chunk: usize = @truncate(value >> shift);";
     "        const part = asm (""""";
     "            : [mask] ""=r"" (-> usize),";
     "            : [value] ""0"" (chunk),";
     "        );";
     "        mask |= @as(" ++ ty ++ ", part) << shift;";
     "    }";
     "    return mask;";
     "}"]%string.

  (* A full-width unsigned mask selects a word without branches. *)
  Definition cmov_helper
             {language_naming_conventions : language_naming_conventions_opt}
             (internal_private : bool) (prefix : string) (t : int.type) : list string :=
    let ty := int_type_to_string t in
    ["";
     "/// Select arg2 when arg1 is zero and arg3 otherwise, using a bit mask.";
     (if internal_private then "fn " else "pub fn ") ++
       ToString.format_special_function_name_ty internal_private prefix "cmovznz" t ++
       "(out1: *" ++ ty ++ ", arg1: u1, arg2: " ++ ty ++ ", arg3: " ++ ty ++ ") void {";
     "    @setRuntimeSafety(mode == .debug);";
     "";
     "    const mask = " ++
       ToString.format_special_function_name_ty internal_private prefix "selection_mask" t ++ "(arg1);";
     "    out1.* = arg2 ^ ((arg2 ^ arg3) & mask);";
     "}"]%string.

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
         "const mode = @import(""builtin"").mode; // Checked arithmetic is disabled in non-debug modes to avoid side channels";
         ""]
          ++ (if skip_typedefs
              then []
              else List.flat_map
                     (fun td_name =>
                        match List.find (fun '(name, _, _, _) => (td_name =? name)%string) typedef_map with
                        | Some td_info => [""] ++ make_typedef prefix private td_info
                        | None => ["@compilerError(""Could not find typedef info for '" ++ td_name ++ "'"");"]%string
                        end%list)
                     (typedefs_used infos))
          ++ List.flat_map (fun bw => carry_helpers internal_private prefix (Z.pos bw))
                           (List.filter (fun bw => native_split (Z.pos bw))
                                        (PositiveSet.elements (ToString.addcarryx_lg_splits infos)))
          ++ List.flat_map (fun bw => mul_helper internal_private prefix (Z.pos bw))
                           (List.filter (fun bw => native_split (Z.pos bw))
                                        (PositiveSet.elements (ToString.mulx_lg_splits infos)))
          ++ List.flat_map (fun t => selection_mask_helper internal_private prefix t
                                    ++ cmov_helper internal_private prefix t)%list
                           (List.filter int.is_unsigned
                                        (ToString.IntSet.elements (ToString.cmovznz_bitwidths infos))))%list.

  (* Integer literal to string *)
  Definition int_literal_to_string (prefix : string) (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t with
    | IR.type.Z => HexString.of_Z v (* Zig can automatically figure out the size of integer literals *)
    | IR.type.Zptr => "@compilerError(""literal address " ++ HexString.of_Z v ++ """);"
    end.

  Import IR.Notations.

  Fixpoint literal_through_cast {t} (e : IR.arith_expr t) : option Z :=
    match e with
    | (IR.literal v @@@ _) => Some v
    | (IR.Z_static_cast ty @@@ e) =>
      match literal_through_cast e with
      | Some v =>
        if (0 <=? v)%Z && (v <? 2 ^ (int.bitwidth_of ty - if int.is_signed ty then 1 else 0))%Z
        then Some v else None
      | None => None
      end
    | _ => None
    end%Cexpr.

  (* Types are already known in the IR.  Keep them while printing, rather
     than asking a generic Zig function to rediscover them at comptime. *)
  Definition type_env := list (string * option int.type).
  Definition lookup_type (env : type_env) (name : string) : option int.type :=
    match List.find (fun '(n, _) => (n =? name)%string) env with
    | Some (_, ty) => ty
    | None => None
    end.

  Definition union_types (a b : option int.type) : option int.type :=
    match a, b with
    | Some a, Some b => Some (int.union a b)
    | Some a, None => Some a
    | None, b => b
    end.

  Fixpoint arith_type {t} (env : type_env) (e : IR.arith_expr t) : option int.type :=
    match e with
    | IR.Var _ name => lookup_type env name
    | (IR.Z_static_cast ty @@@ _) => Some ty
    | (IR.Z_bneg @@@ _) => Some _Bool
    | (IR.Z_lnot ty @@@ _) | (IR.Z_value_barrier ty @@@ _) => Some ty
    | (IR.List_nth _ @@@ e) | (IR.Dereference @@@ e) | (IR.Addr @@@ e)
    | (IR.Z_shiftr _ @@@ e) | (IR.Z_shiftl _ @@@ e) => arith_type env e
    | (IR.Z_land @@@ (a, b)) | (IR.Z_lor @@@ (a, b)) | (IR.Z_lxor @@@ (a, b))
    | (IR.Z_add @@@ (a, b)) | (IR.Z_sub @@@ (a, b)) | (IR.Z_mul @@@ (a, b)) =>
      union_types (arith_type env a) (arith_type env b)
    | _ => None
    end%Cexpr.

  Definition same_type (a b : int.type) : bool :=
    Bool.eqb (int.is_signed a) (int.is_signed b) &&
    (int.bitwidth_of a =? int.bitwidth_of b)%Z.

  Definition has_type (expected : option int.type) (ty : int.type) : bool :=
    match expected with Some t => same_type t ty | None => false end.

  (* Peer type resolution widens the smaller operand.  This is separate
     from a result-type context: a peer cannot infer the result type of
     @truncate or @bitCast.  Only remove value-preserving widening casts. *)
  Definition peer_widens_cast {t} (env : type_env) (peer : option int.type)
             (dest : int.type) (e : IR.arith_expr t) : bool :=
    match peer with
    | Some peer =>
      int.is_tighter_than dest peer &&
      match arith_type env e with
      | Some source => int.is_tighter_than source dest
      | None =>
        match literal_through_cast e with
        | Some v =>
          ((if int.is_signed dest then -2 ^ (int.bitwidth_of dest - 1) else 0) <=? v)%Z &&
          (v <? 2 ^ (int.bitwidth_of dest - if int.is_signed dest then 1 else 0))%Z
        | None => false
        end
      end
    | None => false
    end.

  Fixpoint operand_type {t} (env : type_env) (peer : option int.type)
           (e : IR.arith_expr t) : option int.type :=
    match e with
    | (IR.Z_static_cast dest @@@ inner) =>
      if peer_widens_cast env peer dest inner
      then operand_type env peer inner else Some dest
    | _ => arith_type env e
    end%Cexpr.

  Definition operand_peers {a b} (env : type_env)
             (x : IR.arith_expr a) (y : IR.arith_expr b)
    : option int.type * option int.type :=
    let tx := arith_type env x in
    let ty := arith_type env y in
    let result := union_types tx ty in
    match result with
    | Some result_ty =>
      if has_type (operand_type env result x) result_ty ||
         has_type (operand_type env result y) result_ty
      then (result, result)
      (* If both operands were widened, keep one explicit widening so
         the operation itself still computes at the original width. *)
      else if has_type tx result_ty then (None, result)
      else if has_type ty result_ty then (result, None)
      else (None, None)
    | None => (None, None)
    end.

  Definition typed_result {language_naming_conventions : language_naming_conventions_opt}
             (expected : option int.type) (ty : int.type) (s : string) : string :=
    if has_type expected ty then s
    else "@as(" ++ int_type_to_string ty ++ ", " ++ s ++ ")".

  Definition cast_to_string {language_naming_conventions : language_naming_conventions_opt}
             (expected source : option int.type) (dest : int.type) (s : string) : string :=
    match source with
    | None => typed_result expected dest s
    | Some source =>
      if same_type source dest then s
      else if (int.bitwidth_of dest <? int.bitwidth_of source)%Z then
        if Bool.eqb (int.is_signed source) (int.is_signed dest)
        then typed_result expected dest ("@truncate(" ++ s ++ ")")
        else let narrow := int.of_lgbitwidth (int.is_signed source) (int.lgbitwidth_of dest) in
             typed_result expected dest
               ("@bitCast(@as(" ++ int_type_to_string narrow ++ ", @truncate(" ++ s ++ ")))" )
      else if int.is_signed source && int.is_unsigned dest then
        typed_result expected dest
          ("@bitCast(" ++
           (if (int.bitwidth_of source =? int.bitwidth_of dest)%Z then s
            else typed_result None (int.signed_counterpart_of dest) s) ++ ")")
      else if (int.bitwidth_of source =? int.bitwidth_of dest)%Z then
        typed_result expected dest ("@bitCast(" ++ s ++ ")")
      else typed_result expected dest s
    end.

  (* Primitive carry inputs remain bits even when CLI options widen the
     field API's carry types.  Narrow explicitly at those call boundaries. *)
  Definition boolean_argument_to_string
             {language_naming_conventions : language_naming_conventions_opt}
             (source : option int.type) (s : string) : string :=
    cast_to_string (Some _Bool) source _Bool s.

  Fixpoint arith_to_string_with_peer
           {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
           (prefix : string) (env : type_env) (expected peer : option int.type)
           {t} (e : IR.arith_expr t) {struct e} : string
    := let special_name_ty name ty := ToString.format_special_function_name_ty internal_private prefix name ty in
       let special_name name bw := ToString.format_special_function_name internal_private prefix name false(*unsigned*) bw in
       match e with
       (* integer literals *)
       | (IR.literal v @@@ _) => int_literal_to_string prefix IR.type.Z v
       (* array dereference *)
       | (IR.List_nth n @@@ IR.Var _ v) => v ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "]"
       (* (de)referencing *)
       | (IR.Addr @@@ IR.Var _ v) => "&" ++ v
       | (IR.Dereference @@@ IR.Var _ v) => v ++ ".*"
       | (IR.Dereference @@@ e) => "( " ++ arith_to_string_with_peer internal_private prefix env None None e ++ ".* )"
       (* bitwise operations *)
       | (IR.Z_shiftr offset @@@ e) =>
         "(" ++ arith_to_string_with_peer internal_private prefix env None None e ++ " >> " ++ Decimal.Z.to_string offset ++ ")"
       | (IR.Z_shiftl offset @@@ e) =>
         "(" ++ arith_to_string_with_peer internal_private prefix env None None e ++ " << " ++ Decimal.Z.to_string offset ++ ")"
       | (IR.Z_land @@@ (e1, e2)) =>
         let '(p1, p2)%core := operand_peers env e1 e2 in
         "(" ++ arith_to_string_with_peer internal_private prefix env None p1 e1 ++ " & " ++ arith_to_string_with_peer internal_private prefix env None p2 e2 ++ ")"
       | (IR.Z_lor @@@ (e1, e2)) =>
         let '(p1, p2)%core := operand_peers env e1 e2 in
         "(" ++ arith_to_string_with_peer internal_private prefix env None p1 e1 ++ " | " ++ arith_to_string_with_peer internal_private prefix env None p2 e2 ++ ")"
       | (IR.Z_lxor @@@ (e1, e2)) =>
         let '(p1, p2)%core := operand_peers env e1 e2 in
         "(" ++ arith_to_string_with_peer internal_private prefix env None p1 e1 ++ " ^ " ++ arith_to_string_with_peer internal_private prefix env None p2 e2 ++ ")"
       | (IR.Z_lnot _ @@@ e) => "(~" ++ arith_to_string_with_peer internal_private prefix env None None e ++ ")"
       (* arithmetic operations *)
       | (IR.Z_add @@@ (x1, x2)) =>
         let '(p1, p2)%core := operand_peers env x1 x2 in
         "(" ++ arith_to_string_with_peer internal_private prefix env None p1 x1 ++ " + " ++ arith_to_string_with_peer internal_private prefix env None p2 x2 ++ ")"
       | (IR.Z_mul @@@ (x1, x2)) =>
         let '(p1, p2)%core := operand_peers env x1 x2 in
         "(" ++ arith_to_string_with_peer internal_private prefix env None p1 x1 ++ " * " ++ arith_to_string_with_peer internal_private prefix env None p2 x2 ++ ")"
       | (IR.Z_sub @@@ (x1, x2)) =>
         let '(p1, p2)%core := operand_peers env x1 x2 in
         "(" ++ arith_to_string_with_peer internal_private prefix env None p1 x1 ++ " - " ++ arith_to_string_with_peer internal_private prefix env None p2 x2 ++ ")"
       | (IR.Z_bneg @@@ (IR.Z_bneg @@@ e)) =>
         if has_type (arith_type env e) _Bool
         then arith_to_string_with_peer internal_private prefix env expected None e
         else "@intFromBool(" ++ arith_to_string_with_peer internal_private prefix env None None e ++ " != 0)"
       | (IR.Z_bneg @@@ e) => "@intFromBool(" ++ arith_to_string_with_peer internal_private prefix env None None e ++ " == 0)"
       | (IR.Z_mul_split lg2s @@@ ((out1, out2), (a, b))) =>
         let ty := Some (int.of_bitwidth_up false lg2s) in
         special_name "mulx" lg2s ++ "(" ++
         arith_to_string_with_peer internal_private prefix env None None out1 ++ ", " ++
         arith_to_string_with_peer internal_private prefix env None None out2 ++ ", " ++
         arith_to_string_with_peer internal_private prefix env ty None a ++ ", " ++
         arith_to_string_with_peer internal_private prefix env ty None b ++ ")"
       | (IR.Z_add_with_get_carry lg2s @@@ ((out1, out2), (c, a, b))) =>
         let ty := Some (int.of_bitwidth_up false lg2s) in
         special_name "addcarryx" lg2s ++ "(" ++
         arith_to_string_with_peer internal_private prefix env None None out1 ++ ", " ++
         arith_to_string_with_peer internal_private prefix env None None out2 ++ ", " ++
         boolean_argument_to_string (arith_type env c)
           (arith_to_string_with_peer internal_private prefix env (Some _Bool) None c) ++ ", " ++
         arith_to_string_with_peer internal_private prefix env ty None a ++ ", " ++
         arith_to_string_with_peer internal_private prefix env ty None b ++ ")"
       | (IR.Z_sub_with_get_borrow lg2s @@@ ((out1, out2), (c, a, b))) =>
         let ty := Some (int.of_bitwidth_up false lg2s) in
         special_name "subborrowx" lg2s ++ "(" ++
         arith_to_string_with_peer internal_private prefix env None None out1 ++ ", " ++
         arith_to_string_with_peer internal_private prefix env None None out2 ++ ", " ++
         boolean_argument_to_string (arith_type env c)
           (arith_to_string_with_peer internal_private prefix env (Some _Bool) None c) ++ ", " ++
         arith_to_string_with_peer internal_private prefix env ty None a ++ ", " ++
         arith_to_string_with_peer internal_private prefix env ty None b ++ ")"
       | (IR.Z_zselect ty @@@ (out, (c, a, b))) =>
         special_name_ty "cmovznz" ty ++ "(" ++
         arith_to_string_with_peer internal_private prefix env None None out ++ ", " ++
         boolean_argument_to_string (arith_type env c)
           (arith_to_string_with_peer internal_private prefix env (Some _Bool) None c) ++ ", " ++
         arith_to_string_with_peer internal_private prefix env (Some ty) None a ++ ", " ++
         arith_to_string_with_peer internal_private prefix env (Some ty) None b ++ ")"
       | (IR.Z_mul_split lg2s @@@ args) =>
         special_name "mulx" lg2s ++ "(" ++ arith_to_string_with_peer internal_private prefix env None None args ++ ")"
       | (IR.Z_add_with_get_carry lg2s @@@ args) =>
         special_name "addcarryx" lg2s ++ "(" ++ arith_to_string_with_peer internal_private prefix env None None args ++ ")"
       | (IR.Z_sub_with_get_borrow lg2s @@@ args) =>
         special_name "subborrowx" lg2s ++ "(" ++ arith_to_string_with_peer internal_private prefix env None None args ++ ")"
       | (IR.Z_zselect ty @@@ args) =>
         special_name_ty "cmovznz" ty ++ "(" ++ arith_to_string_with_peer internal_private prefix env None None args ++ ")"
       | (IR.Z_value_barrier ty @@@ args) =>
         special_name_ty "value_barrier" ty ++ "(" ++ arith_to_string_with_peer internal_private prefix env None None args ++ ")"
       (* A cast to an unsigned limb already keeps its low bits.  Drop
          the full-width mask commonly emitted before a narrowing cast.
          Keep partial masks, which may clear additional bits. *)
       | (IR.Z_static_cast narrow @@@ (IR.Z_sub @@@ (zero, IR.Z_static_cast wide @@@ bit))) =>
         if same_type narrow (int.signed_counterpart_of _Bool) &&
            has_type (arith_type env bit) _Bool &&
            (match literal_through_cast zero with Some z => (z =? 0)%Z | None => false end)
         then typed_result expected narrow
                ("@bitCast(" ++ arith_to_string_with_peer internal_private prefix env None None bit ++ ")")
         else cast_to_string expected (union_types (arith_type env zero) (Some wide)) narrow
                ("(" ++ arith_to_string_with_peer internal_private prefix env None None zero ++ " - " ++
                  cast_to_string None (arith_type env bit) wide
                    (arith_to_string_with_peer internal_private prefix env None None bit) ++ ")")
       | (IR.Z_static_cast int_t @@@ (IR.Z_land @@@ (e1, e2))) =>
         match literal_through_cast e2 with
         | Some mask =>
           if int.is_unsigned int_t && (mask =? 2 ^ int.bitwidth_of int_t - 1)%Z
           then match e1 with
                | (IR.Z_static_cast mid @@@ inner) =>
                  match arith_type env inner with
                  | Some source =>
                    if (int.bitwidth_of int_t <=? int.bitwidth_of mid)%Z
                    then cast_to_string expected (Some source) int_t
                           (arith_to_string_with_peer internal_private prefix env None None inner)
                    else cast_to_string expected (Some mid) int_t
                           (arith_to_string_with_peer internal_private prefix env None None e1)
                  | None => cast_to_string expected (Some mid) int_t
                              (arith_to_string_with_peer internal_private prefix env None None e1)
                  end
                | _ => cast_to_string expected (arith_type env e1) int_t
                         (arith_to_string_with_peer internal_private prefix env None None e1)
                end
           else let '(p1, p2)%core := operand_peers env e1 e2 in
                  cast_to_string expected
                  (union_types (arith_type env e1) (arith_type env e2)) int_t
                  ("(" ++ arith_to_string_with_peer internal_private prefix env None p1 e1 ++ " & " ++ arith_to_string_with_peer internal_private prefix env None p2 e2 ++ ")")
         | None => let '(p1, p2)%core := operand_peers env e1 e2 in
                  cast_to_string expected
                     (union_types (arith_type env e1) (arith_type env e2)) int_t
                     ("(" ++ arith_to_string_with_peer internal_private prefix env None p1 e1 ++ " & " ++ arith_to_string_with_peer internal_private prefix env None p2 e2 ++ ")")
         end
       | (IR.Z_static_cast int_t @@@ e) =>
         if peer_widens_cast env peer int_t e
         then arith_to_string_with_peer internal_private prefix env expected peer e
         else match e with
         | (IR.Z_static_cast mid @@@ inner) =>
           (* Keeping only the low destination bits makes an intermediate
              cast to at least that width redundant.  In particular this
              avoids widening sign masks to double width and truncating
              them back to a limb. *)
           match arith_type env inner with
           | Some source =>
             if (int.bitwidth_of int_t <=? int.bitwidth_of mid)%Z
             then cast_to_string expected (Some source) int_t
                    (arith_to_string_with_peer internal_private prefix env None None inner)
             else cast_to_string expected (Some mid) int_t
                    (arith_to_string_with_peer internal_private prefix env None None e)
           | None => cast_to_string expected (Some mid) int_t
                       (arith_to_string_with_peer internal_private prefix env None None e)
           end
         | _ => cast_to_string expected (arith_type env e) int_t
                  (arith_to_string_with_peer internal_private prefix env None None e)
         end
       | IR.Var _ v => v
       | IR.Pair A B a b => arith_to_string_with_peer internal_private prefix env None None a ++ ", " ++ arith_to_string_with_peer internal_private prefix env None None b
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

  Definition arith_to_string
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (prefix : string) (env : type_env) (expected : option int.type)
             {t} (e : IR.arith_expr t) : string :=
    arith_to_string_with_peer internal_private prefix env expected None e.

  Definition stmt_to_string
             {language_naming_conventions : language_naming_conventions_opt} (internal_private : bool)
             (prefix : string) (env : type_env) (e : IR.stmt) : string :=
    match e with
    | IR.Call val => arith_to_string internal_private prefix env None val ++ ";"
    | IR.Assign true t sz name val =>
      (* local non-mutable declaration with initialization *)
      "const " ++ name ++
        (match sz with Some ty => ": " ++ primitive_type_to_string t sz | None => "" end) ++
        " = " ++ arith_to_string internal_private prefix env sz val ++ ";"
    | IR.Assign false _ sz name val =>
    (* code : name ++ " = " ++ arith_to_string internal_private prefix val ++ ";" *)
      "@compilerError(""trying to assign value to non-mutable variable"");"
    | IR.AssignZPtr name sz val =>
      name ++ ".* = " ++ arith_to_string internal_private prefix env sz val ++ ";"
    | IR.DeclareVar t sz name =>
      "var " ++ name ++ ": " ++ primitive_type_to_string t sz ++ " = undefined;"
    | IR.Comment lines _ =>
      String.concat String.NewLine (comment_block (ToString.preprocess_comment_block lines))
    | IR.AssignNth name n val =>
      name ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "] = " ++ arith_to_string internal_private prefix env (lookup_type env name) val ++ ";"
    end.

  (* Share a mask between adjacent selections of the same immutable selector.
     Declarations and comments cannot change it; every other statement clears
     the cache, including calls which may write through pointers. *)
  Fixpoint to_strings_with_mask {language_naming_conventions : language_naming_conventions_opt}
           (internal_private : bool) (prefix : string) (env : type_env)
           (cached : option (string * string * string)) (e : IR.expr) : list string :=
    match e with
    | [] => []
    | stmt :: rest =>
      let env' := match stmt with
                  | IR.Assign _ _ sz name _ | IR.DeclareVar _ sz name => (name, sz) :: env
                  | _ => env
                  end in
      match stmt with
      | IR.Call (IR.Z_zselect ty @@@
          ((IR.Addr @@@ IR.Var _ out), (IR.Var _ c, a, b))) =>
        if int.is_unsigned ty then
          let ty_s := int_type_to_string ty in
          let previous := match cached with
                          | Some (c', ty', mask) =>
                            if (c =? c')%string && (ty_s =? ty')%string
                            then Some mask else None
                          | None => None
                          end in
          let mask := match previous with
                      | Some mask => mask
                      | None => (out ++ "_selection_mask")%string
                      end in
          let init := match previous with
                      | Some _ => []
                      | None => ["const " ++ mask ++ " = " ++
                        ToString.format_special_function_name_ty internal_private prefix "selection_mask" ty ++
                        "(" ++ boolean_argument_to_string (lookup_type env c) c ++ ");"]%string
                      end in
          let a_s := arith_to_string internal_private prefix env (Some ty) a in
          let b_s := arith_to_string internal_private prefix env (Some ty) b in
          (init ++ [out ++ " = " ++ a_s ++ " ^ ((" ++ a_s ++ " ^ " ++ b_s ++ ") & " ++ mask ++ ");"]%string ++
            to_strings_with_mask internal_private prefix env'
              (if (out =? c)%string then None else Some (c, ty_s, mask)) rest)%list
        else stmt_to_string internal_private prefix env stmt ::
               to_strings_with_mask internal_private prefix env' None rest
      | _ => stmt_to_string internal_private prefix env stmt ::
               to_strings_with_mask internal_private prefix env'
                 (match stmt with
                  | IR.DeclareVar _ _ _ | IR.Comment _ _ => cached
                  | _ => None
                  end) rest
      end
    end.

  Definition to_strings {language_naming_conventions : language_naming_conventions_opt}
           (internal_private : bool) (prefix : string) (env : type_env) (e : IR.expr) : list string :=
    to_strings_with_mask internal_private prefix env None e.

  Import Rewriter.Language.Language.Compilers Crypto.Language.API.Compilers IR.OfPHOAS.
  Local Notation tZ := (base.type.type_base base.type.Z).

  Fixpoint base_arg_types {t} : base_var_data t -> type_env :=
    match t return base_var_data t -> type_env with
    | tZ => fun '(name, _, ty, _) => [(name, ty)]
    | base.type.list tZ => fun '(name, ty, _, _) => [(name, ty)]
    | base.type.prod A B => fun '(a, b) => base_arg_types a ++ base_arg_types b
    | _ => fun _ => []
    end%list.

  Definition arg_types {t} : var_data t -> type_env :=
    match t return var_data t -> type_env with
    | type.base _ => base_arg_types
    | _ => fun _ => []
    end.

  Fixpoint input_types {t} : type.for_each_lhs_of_arrow var_data t -> type_env :=
    match t return type.for_each_lhs_of_arrow var_data t -> type_env with
    | type.base _ => fun _ => []
    | type.arrow _ _ => fun '(a, rest) => arg_types a ++ input_types rest
    end%list.

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
    ((if private then "fn " else "pub fn ") ++ name ++
      "(" ++ String.concat ", " (to_arg_list internal_private all_private prefix Out rets ++ to_arg_list_for_each_lhs_of_arrow internal_private all_private prefix args) ++
      ") void {")%string :: (["    @setRuntimeSafety(mode == .debug);"; ""]%string)%list ++ (List.map (fun s => "    " ++ s)%string (to_strings internal_private prefix (input_types args ++ arg_types rets)%list body)) ++ ["}"%string]%list.

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
       ToString.strip_special_infos machine_wordsize infos :=
         ToString.ident_info_with_cmovznz
           (ToString.ident_info_with_mulx
             (ToString.ident_info_with_addcarryx infos
               (PositiveSet.filter (fun bw => negb (native_split (Z.pos bw)))
                                   (ToString.addcarryx_lg_splits infos)))
             (PositiveSet.filter (fun bw => negb (native_split (Z.pos bw)))
                                 (ToString.mulx_lg_splits infos)))
           (ToString.IntSet.filter int.is_signed (ToString.cmovznz_bitwidths infos)) |}.

  Lemma xor_selection_equivalent (a b mask : Z) :
    Z.lxor a (Z.land (Z.lxor a b) mask)
    = Z.lor (Z.land (Z.lnot mask) a) (Z.land mask b).
  Proof.
    apply Z.bits_inj'; intros n Hn.
    rewrite Z.lxor_spec, Z.lor_spec, !Z.land_spec, Z.lxor_spec, Z.lnot_spec by assumption.
    destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit mask n); reflexivity.
  Qed.

  Section CastTests.
    Local Instance naming : language_naming_conventions_opt := default_language_naming_conventions.

    Definition test_selection (out c : string) : IR.stmt :=
      IR.Call (IR.Z_zselect uint64 @@@
        (IR.Addr @@@ IR.Var IR.type.Z out,
         (IR.Var IR.type.Z c, IR.Var IR.type.Z "a", IR.Var IR.type.Z "b")))%Cexpr.

    Example adjacent_selections_share_mask :
      to_strings true "" [("c", Some _Bool); ("a", Some uint64); ("b", Some uint64)]
        [test_selection "x1" "c"; IR.DeclareVar IR.type.Z (Some uint64) "x2";
         test_selection "x2" "c"]
      = ["const x1_selection_mask = selection_mask_u64(c);";
         "x1 = a ^ ((a ^ b) & x1_selection_mask);";
         "var x2: u64 = undefined;";
         "x2 = a ^ ((a ^ b) & x1_selection_mask);"].
    Proof. reflexivity. Qed.

    Example writing_selector_invalidates_mask :
      to_strings true "" [("c", Some uint64); ("a", Some uint64); ("b", Some uint64)]
        [test_selection "c" "c"; test_selection "x2" "c"]
      = ["const c_selection_mask = selection_mask_u64(@truncate(c));";
         "c = a ^ ((a ^ b) & c_selection_mask);";
         "const x2_selection_mask = selection_mask_u64(@truncate(c));";
         "x2 = a ^ ((a ^ b) & x2_selection_mask);"].
    Proof. reflexivity. Qed.

    Example pointer_writes_invalidate_mask :
      List.nth 3
        (to_strings true "" [("c", Some _Bool); ("a", Some uint64); ("b", Some uint64)]
          [test_selection "x1" "c";
           IR.AssignZPtr "p" (Some uint64) (IR.Var IR.type.Z "a");
           test_selection "x2" "c"]) ""
      = "const x2_selection_mask = selection_mask_u64(c);".
    Proof. reflexivity. Qed.

    Example widened_api_carry_is_narrowed_at_call :
      boolean_argument_to_string (Some uint8) "c" = "@truncate(c)".
    Proof. reflexivity. Qed.

    Example bit_carry_needs_no_cast :
      boolean_argument_to_string (Some _Bool) "c" = "c".
    Proof. reflexivity. Qed.

    Example inferred_widening :
      cast_to_string (Some uint64) (Some uint32) uint64 "x" = "x".
    Proof. reflexivity. Qed.

    Example explicit_widening :
      cast_to_string None (Some uint32) uint64 "x" = "@as(u64, x)".
    Proof. reflexivity. Qed.

    Example inferred_truncation :
      cast_to_string (Some uint64) (Some uint128) uint64 "x" = "@truncate(x)".
    Proof. reflexivity. Qed.

    Example sign_extension_before_reinterpretation :
      cast_to_string (Some uint64) (Some (int.of_bitwidth true 1)) uint64 "x" = "@bitCast(@as(i64, x))".
    Proof. reflexivity. Qed.

    Example same_width_reinterpretation :
      cast_to_string (Some int64) (Some uint64) int64 "x" = "@bitCast(x)".
    Proof. reflexivity. Qed.

    Example boolean_negation :
      arith_to_string true "" [("x", Some uint64)] (Some _Bool)
        (IR.Z_bneg @@@ IR.Var IR.type.Z "x")%Cexpr = "@intFromBool(x == 0)".
    Proof. reflexivity. Qed.

    Example full_mask_is_redundant :
      arith_to_string true "" [("x", Some uint128)] (Some uint64)
        (IR.Z_static_cast uint64 @@@
          (IR.Z_land @@@ (IR.Var IR.type.Z "x",
            IR.Z_static_cast uint128 @@@ (IR.literal (2^64-1) @@@ IR.TT))))%Cexpr
      = "@truncate(x)".
    Proof. vm_compute. reflexivity. Qed.

    Example partial_mask_is_preserved :
      arith_to_string true "" [("x", Some uint128)] (Some uint64)
        (IR.Z_static_cast uint64 @@@
          (IR.Z_land @@@ (IR.Var IR.type.Z "x",
            IR.Z_static_cast uint128 @@@ (IR.literal 255 @@@ IR.TT))))%Cexpr
      = "@truncate((x & 0xff))".
    Proof. vm_compute. reflexivity. Qed.

    Example peer_infers_left_widening :
      arith_to_string true "" [("x", Some uint32); ("y", Some uint64)] (Some uint64)
        (IR.Z_add @@@ (IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "x",
                       IR.Var IR.type.Z "y"))%Cexpr = "(x + y)".
    Proof. vm_compute. reflexivity. Qed.

    Example peer_infers_right_widening :
      arith_to_string true "" [("x", Some uint64); ("y", Some uint32)] (Some uint64)
        (IR.Z_sub @@@ (IR.Var IR.type.Z "x",
                       IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "y"))%Cexpr = "(x - y)".
    Proof. vm_compute. reflexivity. Qed.

    Example wide_product_keeps_one_widening :
      arith_to_string true "" [("x", Some uint64); ("y", Some uint64)] (Some uint128)
        (IR.Z_mul @@@ (IR.Z_static_cast uint128 @@@ IR.Var IR.type.Z "x",
                       IR.Z_static_cast uint128 @@@ IR.Var IR.type.Z "y"))%Cexpr
      = "(@as(u128, x) * y)".
    Proof. vm_compute. reflexivity. Qed.

    Example peer_infers_literal_type :
      arith_to_string true "" [("x", Some uint64)] (Some uint64)
        (IR.Z_lxor @@@ (IR.Var IR.type.Z "x",
                        IR.Z_static_cast uint64 @@@ (IR.literal 255 @@@ IR.TT)))%Cexpr
      = "(x ^ 0xff)".
    Proof. vm_compute. reflexivity. Qed.

    Example peer_does_not_infer_truncation :
      arith_to_string true "" [("x", Some uint128); ("y", Some uint64)] (Some uint64)
        (IR.Z_add @@@ (IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "x",
                       IR.Var IR.type.Z "y"))%Cexpr
      = "(@as(u64, @truncate(x)) + y)".
    Proof. vm_compute. reflexivity. Qed.

    Example peer_does_not_infer_reinterpretation :
      arith_to_string true "" [("x", Some int64); ("y", Some uint64)] (Some uint64)
        (IR.Z_add @@@ (IR.Z_static_cast uint64 @@@ IR.Var IR.type.Z "x",
                       IR.Var IR.type.Z "y"))%Cexpr
      = "(@as(u64, @bitCast(x)) + y)".
    Proof. vm_compute. reflexivity. Qed.

    Example peer_preserves_out_of_range_literal_cast :
      peer_widens_cast [] (Some uint64) uint8
        (IR.literal 65535 @@@ IR.TT)%Cexpr = false.
    Proof. vm_compute. reflexivity. Qed.

    Example narrowing_masks_are_not_literals :
      literal_through_cast (IR.Z_static_cast uint8 @@@ (IR.literal 65535 @@@ IR.TT))%Cexpr = None.
    Proof. vm_compute. reflexivity. Qed.

    Example nonstandard_split_uses_generic_arithmetic : native_split 56 = false.
    Proof. reflexivity. Qed.
  End CastTests.

End Zig.
