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

Module JSON.
  Definition indent (indent : string) : list string -> list string
    := List.map (fun s => indent ++ s)%string.

  Definition int_bitwidth_to_string (signed : bool) (bitwidth : Z) : string :=
    ((if signed then "i" else "u")
       ++ Decimal.Z.to_string bitwidth)%string.

  Definition int_type_to_string (t : ToString.int.type) : string :=
    int_bitwidth_to_string (ToString.int.is_signed t) (ToString.int.bitwidth_of t).

  Definition primitive_type_to_string (t : IR.type.primitive)
             (r : option ToString.int.type) : string :=
    match t with
    | IR.type.Zptr => "*"
    | IR.type.Z => ""
    end ++ match r with
           | Some int_t => int_type_to_string int_t
           | None => "(auto)"
           end.

  Definition int_literal_to_string (t : IR.type.primitive) (v : BinInt.Z) : string :=
    match t with
    | IR.type.Z => HexString.of_Z v
    | IR.type.Zptr => "#error ""literal address " ++ HexString.of_Z v ++ """;"
    end.

  Import IR.Notations.

  Record op_data :=
    { datatype : string ; name : list string ; operation : string ; parameters : list (string * string) ; arguments : list (list string) }.

  Definition comma_concat (ls : list (list string)) : list string
    := let ret := List.flat_map (fun s => match s with
                                          | [] => []
                                          | _ => s ++ [","]
                                          end) ls in
       (* drop the final , *)
       List.firstn (List.length ret - 1) ret.

  Definition op_data_to_JSON (v : op_data) : list string
    := (["{"
         ; " ""datatype"": """ ++ v.(datatype) ++ ""","
         ; " ""name"": [" ++ String.concat ", " (List.map (fun n => """" ++ n ++ """")%string v.(name)) ++ "],"
         ; " ""operation"": """ ++ v.(operation) ++ ""","
         ]%string)
         ++ match v.(parameters) with
            | [] => []
            | _ =>
                [" ""parameters"": {" ++ String.concat ", " (List.map (fun '(n, val) => """" ++ n ++ """: " ++ val)%string v.(parameters)) ++ "},"]%string
            end
         ++ [" ""arguments"": ["]
         ++ (indent "  " (comma_concat v.(arguments)))
         ++ [" ]"
             ; "}"].

  Fixpoint arith_to_string (outargs : list string)
           {t} (sz : option ToString.int.type)
           (e : IR.arith_expr t)
    : list (list string)
    := let handle_op sz op params outargs inargs
           := [op_data_to_JSON
                 {| datatype := match sz with None => "(auto)" | Some ty => int_type_to_string ty end
                    ; name := outargs
                    ; operation := op
                    ; parameters := params
                    ; arguments := inargs |}] in
       let handle_op_size lg2s op outargs inargs
         := handle_op sz op [("size", Decimal.show_Z lg2s)] outargs inargs in
       let handle_op1 op {t} inargs
           := handle_op sz op [] outargs (@arith_to_string [] t sz inargs) in
       let wrap_value res
           := match outargs with
              | [] => res
              | _ => handle_op sz "=" [] outargs res
              end in
       match e with
       (* integer literals *)
       | (IR.literal v @@@ _)
         => wrap_value [ ["""" ++ int_literal_to_string IR.type.Z v ++ """"] ]
       (* array dereference *)
       | (IR.List_nth n @@@ IR.Var _ v)
         => wrap_value [ ["""" ++ v ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "]"""] ]
       (* (de)referencing *)
       | (IR.Addr @@@ IR.Var _ v)
         => wrap_value [ ["""&" ++ v ++ """"] ]
       | (IR.Dereference @@@ IR.Var _ v)
         => wrap_value [ ["""*" ++ v ++ """"] ]
       | (IR.Dereference @@@ e)
         => handle_op sz "dereference" [] [] (arith_to_string [] sz e)
       (* bitwise operations *)
       | (IR.Z_shiftr offset @@@ e)
         => handle_op sz ">>" [] outargs
                      ((arith_to_string [] sz e)
                         ++ [ ["""" ++ Decimal.Z.to_string offset ++ """"]%string ])%list
       | (IR.Z_shiftl offset @@@ e)
         => handle_op sz "<<" [] outargs
                      ((arith_to_string [] sz e)
                         ++ [ ["""" ++ Decimal.Z.to_string offset ++ """"]%string ])%list
       | (IR.Z_land @@@ args)
         => handle_op1 "&" args
       | (IR.Z_lor @@@ args)
         => handle_op1 "|" args
       | (IR.Z_lxor @@@ args)
         => handle_op1 "^" args
       | (IR.Z_lnot _ @@@ args)
         => handle_op1 "~" args
       (* arithmetic operations *)
       | (IR.Z_add @@@ args)
         => handle_op1 "+" args
       | (IR.Z_mul @@@ args)
         => handle_op1 "*" args
       | (IR.Z_sub @@@ args)
         => handle_op1 "-" args
       | (IR.Z_bneg @@@ args)
         => handle_op1 "!" args
       | (IR.Z_mul_split lg2s @@@ ((IR.Addr @@@ IR.Var _ x1, IR.Addr @@@ IR.Var _ x2), args))
         => let sz' := Some (int.of_bitwidth_up false lg2s) in
            wrap_value (handle_op_size lg2s "mulx" [x1; x2] (arith_to_string [] sz' args))
       | (IR.Z_add_with_get_carry lg2s @@@ ((IR.Addr @@@ IR.Var _ x1, IR.Addr @@@ IR.Var _ x2), args))
         => let sz' := Some (int.of_bitwidth_up false lg2s) in
            wrap_value (handle_op_size lg2s "addcarryx" [x1; x2] (arith_to_string [] sz' args))
       | (IR.Z_sub_with_get_borrow lg2s @@@ ((IR.Addr @@@ IR.Var _ x1, IR.Addr @@@ IR.Var _ x2), args))
         => let sz' := Some (int.of_bitwidth_up false lg2s) in
            wrap_value (handle_op_size lg2s "subborrowx" [x1; x2] (arith_to_string [] sz' args))
       | (IR.Z_value_barrier ty @@@ args) => arith_to_string outargs sz args
       | (IR.Z_zselect ty @@@ (IR.Addr @@@ IR.Var _ v, args))
         => wrap_value (handle_op (Some ty) "cmovznz" [] [v] (arith_to_string [] (Some ty) args))
       | (IR.Z_static_cast int_t @@@ args)
         => handle_op (Some int_t) "static_cast" [] outargs (arith_to_string [] (Some int_t) args)
       | IR.Var _ v
         => wrap_value [ [ """" ++ v ++ """" ] ]
       | IR.Pair A B a b
         => wrap_value (arith_to_string [] sz a ++ arith_to_string [] sz b)%list
       | (IR.Z_add_modulo @@@ _)
         => wrap_value [ [ "#error addmodulo" ] ]
       | (IR.List_nth _ @@@ _)
       | (IR.Addr @@@ _)
       | (IR.Z_mul_split _ @@@ _)
       | (IR.Z_add_with_get_carry _ @@@ _)
       | (IR.Z_sub_with_get_borrow _ @@@ _)
       | (IR.Z_zselect _ @@@ _)
         => wrap_value [ [ "#error bad_arg" ] ]
       | IR.TT => wrap_value [ [ "#error tt" ] ]
       end%string%Cexpr.

  Definition stmt_to_string (e : IR.stmt) : list string
    := List.concat
         match e with
         | IR.Call val
           => arith_to_string [] None val
         | IR.Assign _ _ sz name val
           => arith_to_string [name] sz val
         | IR.AssignZPtr name sz val
           => arith_to_string [name] sz val
         | IR.AssignNth name n val
           => let name := (name ++ "[" ++ Decimal.Z.to_string (Z.of_nat n) ++ "]")%string in
              arith_to_string [name] None val
         | IR.DeclareVar _ _ _
         | IR.Comment _ _
           => []
         end.

  Definition to_strings (e : IR.expr) : list string :=
    comma_concat (List.map stmt_to_string e).


  Import Rewriter.Language.Language.Compilers Crypto.Language.API.Compilers IR.OfPHOAS.

  Local Notation tZ := (base.type.type_base base.type.Z).
  Local Notation None_object := "null" (only parsing).
  Local Notation quote_string s := ("""" ++ s ++ """")%string (only parsing).

  Fixpoint to_base_arg_list {t} : base_var_data t -> Compilers.ZRange.type.base.option.interp t -> list (string * string * (string * string))
    := let show_Z s := quote_string (Hex.show_Z s) in
       let opt_to_json T f (b : option T) :=
           match b with
           | None => (None_object, None_object)
           | Some v => f v
           end in
       let zrange_to_json b :=
           (show_Z b.(lower), show_Z b.(upper)) in
       let opt_zrange_to_json b :=
           opt_to_json _ zrange_to_json b in
       let opt_zrange_list_to_json ls :=
           let ls := List.map opt_zrange_to_json ls in
           ("[" ++ String.concat ", " (List.map (@fst _ _) ls) ++ "]",
            "[" ++ String.concat ", " (List.map (@snd _ _) ls) ++ "]")%string in
       let opt_opt_zrange_list_to_json ls :=
           opt_to_json _ opt_zrange_list_to_json ls in
       match t return base_var_data t -> Compilers.ZRange.type.base.option.interp t -> _ with
       | tZ
         => fun '(n, is_ptr, r, typedef) b
            => [(primitive_type_to_string IR.type.Z r, n, opt_zrange_to_json b)]
       | base.type.prod A B
         => fun '(va, vb) '(ba, bb) => (@to_base_arg_list A va ba ++ @to_base_arg_list B vb bb)%list
       | base.type.list tZ
         => fun '(n, r, len, typedef) b
            => [(primitive_type_to_string IR.type.Z r ++ "[" ++ Decimal.Z.to_string (Z.of_nat len) ++ "]", n,
                 opt_opt_zrange_list_to_json b)]
       | base.type.list _ => fun _ _ => [("#error ""complex list""", "", (None_object, None_object))]
       | base.type.option _ => fun _ _ => [("#error option", "", (None_object, None_object))]
       | base.type.unit => fun _ _ => [("#error unit", "", (None_object, None_object))]
       | base.type.type_base t => fun _ _ => [("#error " ++ show t, "", (None_object, None_object))]
       end%string.

  Definition to_arg_list {t} : var_data t -> Compilers.ZRange.type.option.interp t -> list (string * string * (string * string)) :=
    match t return var_data t -> Compilers.ZRange.type.option.interp t -> _ with
    | type.base t => to_base_arg_list
    | type.arrow _ _ => fun _ _ => [("#error arrow", "", (None_object, None_object))]
    end%string.

  Fixpoint to_arg_list_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow var_data t -> type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t -> list (string * string * (string * string))
    := match t return type.for_each_lhs_of_arrow _ t -> type.for_each_lhs_of_arrow _ t -> _ with
       | type.base t => fun _ _ => nil
       | type.arrow s d
         => fun '(x, xs) '(b, bs)
            => to_arg_list x b ++ @to_arg_list_for_each_lhs_of_arrow d xs bs
       end%list.

  (** * Language-specific numeric conversions to be passed to the PHOAS -> IR translation *)

  Definition JSON_bin_op_natural_output
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

  Definition JSON_bin_op_casts
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

  Definition JSON_un_op_casts
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

  Local Instance JSONLanguageCasts : LanguageCasts :=
    {| bin_op_natural_output := JSON_bin_op_natural_output
       ; bin_op_casts := JSON_bin_op_casts
       ; un_op_casts := JSON_un_op_casts
       ; upcast_on_assignment := true
       ; upcast_on_funcall := true
       ; explicit_pointer_variables := false
    |}.

  Definition to_function_lines (static : bool) (inline : bool) (name : string)
             {t}
             (inbounds : type.for_each_lhs_of_arrow Compilers.ZRange.type.option.interp t)
             (outbounds : Compilers.ZRange.type.base.option.interp (type.final_codomain t))
             (f : type.for_each_lhs_of_arrow var_data t * var_data (type.base (type.final_codomain t)) * IR.expr)
    : list string :=
    let '(args, rets, body) := f in
    let args_list_to_string ls
        := ("["
              ++ (String.concat
                    ", "
                    (List.map
                       (fun '(typ, name, (lbound, ubound)) => "{""datatype"": """ ++ typ ++ """, ""name"": """ ++ name ++ """, ""lbound"": " ++ lbound ++ ", ""ubound"": " ++ ubound ++ "}")
                       ls))
              ++ "]")%string in
    ["{"]
      ++ (["""operation"": """ ++ name ++ ""","
           ; """arguments"": " ++ args_list_to_string (to_arg_list_for_each_lhs_of_arrow args inbounds) ++ ","
           ; """returns"": " ++ args_list_to_string (to_arg_list rets outbounds) ++ ","
           ; """body"": ["]%string)
      ++ to_strings body
      ++ ["]"
          ; "}"].

  (** We will treat all dead variables as _ *)
  Local Instance : consider_retargs_live_opt := fun _ _ _ => false.
  Local Instance : rename_dead_opt := fun s => "_".
  (** No need to lift declarations to the top *)
  Local Instance : lift_declarations_opt := false.

  Definition ToFunctionLines
             {absint_opts : AbstractInterpretation.Options}
             {relax_zrange : relax_zrange_opt}
             {language_naming_conventions : language_naming_conventions_opt}
             {documentation_options : documentation_options_opt}
             {output_options : output_options_opt}
             (machine_wordsize : Z)
             (do_bounds_check : bool) (internal_static : bool) (static : bool) (all_static : bool) (inline : bool) (prefix : string) (name : string)
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
      inl (to_function_lines
             static inline name
             inbounds
             outbounds
             (indata, outdata, f),
           IR.ident_infos.collect_all_infos f intypedefs outtypedefs)
    | inr nil =>
      inr ("Unknown internal error in converting " ++ name ++ " to JSON")%string
    | inr [err] =>
      inr ("Error in converting " ++ name ++ " to JSON:" ++ String.NewLine ++ err)%string
    | inr errs =>
      inr ("Errors in converting " ++ name ++ " to JSON:" ++ String.NewLine ++ String.concat String.NewLine errs)%string
    end.

  Definition OutputJSONAPI : ToString.OutputLanguageAPI :=
    {| ToString.comment_block _ := [];
       ToString.comment_file_header_block _ := [];
       ToString.ToFunctionLines := @ToFunctionLines;
       ToString.header := fun _ _ _ _ _ _ _ _ _ _ _ => [];
       ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];
       (** No special handling for any functions *)
       ToString.strip_special_infos machine_wordsize infos := infos |}.

End JSON.
