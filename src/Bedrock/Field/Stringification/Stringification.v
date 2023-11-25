Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import bedrock2.Syntax.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Naive coqutil.Map.SortedListWord coqutil.Map.SortedListString.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Stringification.IR.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Arrays.MakeAccessSizes.
Require Import Crypto.Bedrock.Field.Common.Arrays.MakeListLengths.
Require Import Crypto.Bedrock.Field.Common.Names.MakeNames.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Func.
Require Import Crypto.Bedrock.Field.Stringification.FlattenVarData.
Require Import Crypto.Bedrock.Field.Stringification.LoadStoreListVarData.
Require Import Crypto.Stringification.C.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Option.
Import Stringification.Language.Compilers.
Import Stringification.IR.Compilers.ToString.
Import Stringification.C.Compilers.ToString.

Import ListNotations Types.Notations.
Import ToString.OfPHOAS.
Local Open Scope string_scope.
Local Open Scope list_scope.

Section with_parameters.
  Context 
    {width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}.

  Fixpoint make_base_var_data {t}
    : base_ltype t -> list_lengths (type.base t) ->
      option (base_var_data t) :=
    let int_type :=
        ToString.int.unsigned (Z.to_nat width) in
    match t as t0 return
          base_ltype t0 ->
          list_lengths (type.base t0) ->
          option (base_var_data t0) with
    | base.type.prod A B =>
      fun x ll =>
        (x1 <- make_base_var_data (fst x) (fst ll);
           x2 <- make_base_var_data (snd x) (snd ll);
           Some (x1, x2))%option
    | base_Z =>
      fun name _ =>
        let is_pointer := false in (* never a pointer *)
        let typedef := None in (* no typedefs for bedrock2 *)
        Some (name, is_pointer, Some int_type, typedef)
    | base_listZ =>
      fun name len =>
        let typedef := None in (* no typedefs for bedrock2 *)
        Some (name, Some int_type, len, typedef)
    | _ => fun _ _ => None
    end.

  Definition make_var_data {t}
    : ltype t -> list_lengths t -> option (var_data t) :=
    match t with
    | type.base b => make_base_var_data
    | type.arrow _ _ => fun _ _ => None
    end.

  Fixpoint make_var_data_of_args {t}
    : type.for_each_lhs_of_arrow ltype t ->
      type.for_each_lhs_of_arrow list_lengths t ->
      option (type.for_each_lhs_of_arrow var_data t) :=
    match t as t0 return
          type.for_each_lhs_of_arrow ltype t0 ->
          type.for_each_lhs_of_arrow list_lengths t0 ->
          option (type.for_each_lhs_of_arrow var_data t0)
    with
    | type.arrow s d =>
      fun names lengths =>
        (x <- make_var_data (fst names) (fst lengths);
           y <- make_var_data_of_args (snd names) (snd lengths);
           Some (x, y))%option
    | type.base b => fun _ _ => Some tt
    end.

  Definition make_header
             {skip_typedefs : skip_typedefs_opt}
             {t}
             (innames : type.for_each_lhs_of_arrow ltype t)
             (inlengths : type.for_each_lhs_of_arrow list_lengths t)
             (inbounds : type.for_each_lhs_of_arrow
                           ZRange.type.option.interp t)
             (outnames : ltype (type.base (type.final_codomain t)))
             (outlengths : list_lengths (type.base (type.final_codomain t)))
             (outbounds : ZRange.type.option.interp
                            (type.base (type.final_codomain t)))
    : option (list string) :=
    match make_var_data_of_args innames inlengths,
          make_base_var_data outnames outlengths with
    | Some indata, Some outdata =>
      Some (["/*"]
              ++ [" * Input Bounds:"]
              ++ (List.map (fun v => " *   " ++ v)%string
                           (input_bounds_to_string indata inbounds))
              ++ [" * Output Bounds:"]
              ++ (List.map (fun v => " *   " ++ v)%string
                           (bound_to_string outdata outbounds))
              ++ [" */"])
    | _, _ => None
    end.
End with_parameters.

Definition bedrock_func_to_lines (f : string * func)
  : list string :=
  [c_func f].

Definition wrap_call
  {width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}
  `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen add_carryx sub_borrowx error}
           {t}
           (indata : type.for_each_lhs_of_arrow var_data t)
           (outdata : base_var_data (type.final_codomain t))
           (f : string*func)
           (insizes : type.for_each_lhs_of_arrow access_sizes t)
           (outsizes : base_access_sizes (type.final_codomain t))
  : string
  := let part := extract_list_var_data outdata in
     let out_ptrs := flatten_listonly_base_var_data (fst part) in
     let innames := out_ptrs ++ flatten_argnames_of_var_data indata in
     let outnames := flatten_listexcl_base_var_data (snd part) in
     let '(name, (args, rets, _body)) := f in
     (* slightly modified from https://github.com/mit-plv/bedrock2/blob/13365e8113131601a60dd6b6ffddc5a0b92aed58/bedrock2/src/bedrock2/ToCString.v#L151-L154 *)
     let '(precall, all_args)
         := match rets, outnames with
            | nil, _ | _, nil => (name, outnames ++ innames)
            | cons _ _, cons r0 _
              => let r0 := List.last outnames r0 in
                 let outnames' := List.removelast outnames in
                 (("*" ++ print_name r0 ++ " = " ++ print_cast r0 ++ name)%string, outnames' ++ innames)
            end%list in
     ((precall ++ "(")
        ++ (String.concat
              ", "
              (List.map
                 (** TODO: Is there a better way to do this, e.g., pulling from insizes? *)
                 (fun n => "(uintptr_t)" ++ print_name n)
                 all_args))
        ++ ")")%string.

Local Instance Decidable_Bitwidth width
  : Decidable.Decidable (Bitwidth.Bitwidth width).
Proof.
  eapply Decidable.Decidable_iff_to_impl.
  { split. { intros H. split. exact H. } { intros [H]. exact H. } }
  exact _.
Qed.

(** When writing wrapper functions, we first check to see if any of the arguments fit in uint8_t; if not then we use the given bounds relaxation function *)
Notation wrapper_relax_zrange relax_zrange
  := (fun r => Option.value (BoundsPipeline.relax_zrange_gen false (* only signed=false *) [8]%Z r) (relax_zrange r)).

(* TODO: for now, name_list is just ignored -- could probably make it not ignored *)
Definition Bedrock2_ToFunctionLines
           {opts : AbstractInterpretation.Options}
           {relax_zrange : relax_zrange_opt}
           {language_naming_conventions : language_naming_conventions_opt}
           {documentation_options : documentation_options_opt}
           {output_options : output_options_opt}
           (width : Z)
           (do_bounds_check : bool) (internal_static : bool) (static : bool) (all_static : bool) (inline : bool) (prefix : string) (name : string)
           {t}
           (e : @API.Expr t)
           (comment : type.for_each_lhs_of_arrow ToString.OfPHOAS.var_data t ->
                      ToString.OfPHOAS.var_data (type.base (type.final_codomain t)) -> list string)
           (name_list : option (list string))
           (inbounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
           (outbounds : ZRange.type.base.option.interp (type.final_codomain t))
           (intypedefs : type.for_each_lhs_of_arrow var_typedef_data t)
           (outtypedefs : base_var_typedef_data (type.final_codomain t))
  : (list string * ToString.ident_infos) + string
  :=
    match Decidable.dec (0 < width)%Z, Decidable.dec (Bitwidth.Bitwidth width) with
    | left width_pos, left BW =>
      let p : Types.parameters
        (BW:=BW)
        (word:=Naive.word width)
        (locals:=SortedListString.map _)
        (mem:=SortedListWord.map(word_ok:=Naive.ok width width_pos) _ _)
        (env:=SortedListString.map _)
        (ext_spec:=fun _ _ _ _ _ => False)
        (varname_gen := default_varname_gen)
        (add_carryx_funcname := "add_carryx")
        (sub_borrowx_funcname := "sub_borrowx")
        (error := expr.var Defaults.ERROR)
        := tt in
      let innames := make_innames (parameters_sentinel:=p)(inname_gen:=default_inname_gen) t in
      let outnames := make_outnames (outname_gen:=default_outname_gen)
                                    (type.final_codomain t) in
      match list_lengths_from_argbounds inbounds with
      | Some inlengths =>
        match make_access_sizes_args inbounds,
              make_base_access_sizes outbounds with
        | Some insizes, Some outsizes =>
          let out := translate_func
                       e innames inlengths insizes outnames outsizes in
          let f : string*func := (("internal_" ++ name)%string, fst out) in
          let outlengths := snd out in
          if error_free_cmd (snd (snd f))
          then
            match make_header innames inlengths inbounds
                              outnames outlengths outbounds with
            | Some header =>
              match (let relax_zrange : relax_zrange_opt := wrapper_relax_zrange relax_zrange in
                     IR.OfPHOAS.var_data_of_PHOAS_bounds e name_list inbounds outbounds intypedefs outtypedefs) with
              | inl (indata, outdata)
                => inl ((header ++ ["static"] ++ bedrock_func_to_lines f)
                          ++ ["/* NOTE: The following wrapper function is not covered by Coq proofs */"
                              ; (((if inline then "__inline__ " else "") ++ (if static then "static " else "") ++ "void " ++ name ++ "(")
                                   ++ (String.concat ", " (C.to_retarg_list prefix outdata ++ C.to_arg_list_for_each_lhs_of_arrow prefix indata))
                                   ++ ") {")
                              ; "  " ++ (wrap_call indata outdata f insizes outsizes) ++ ";"
                              ; "}"
                              ; ""
                             ]%string%list,
                        ToString.ident_info_empty)
              | inr errs => inr (String.concat String.NewLine errs)
              end
            | None =>
              inr
                (String.concat
                   String.NewLine
                   ("Failed to generate header for function:"
                      :: bedrock_func_to_lines f))
            end
          else
            let header :=
                match make_header innames inlengths inbounds
                                  outnames outlengths outbounds with
                | Some x => x | None => [] end in
            inr
              (String.concat
                 String.NewLine
                 (["ERROR-CONTAINING OUTPUT:"]
                    ++ header
                    ++ bedrock_func_to_lines f
                    ++ ["Error occured during translation to bedrock2. This is likely because a part of the input expression either had unsupported integer types (bedrock2 requires that all integers have the same size) or contained an unsupported operation."]))
        | None, _ => inr ("Error determining argument sizes for input bounds. Please check that the bounds fit within the machine word size.")
        | _, None => inr ("Error determining argument sizes for output bounds. Please check that the bounds fit within the machine word size.")
        end
      | None =>
        inr ("Error determining argument lengths from input bounds")
      end
    | _,_ => inr ("Only 32-bit and 64-bit targets are supported")
    end.

Definition OutputBedrock2API : ToString.OutputLanguageAPI :=
  {|
    ToString.comment_block s
    := List.map (fun line => "/* " ++ line ++ " */")%string s;

    ToString.comment_file_header_block s
    := List.map (fun line => "/* " ++ line ++ " */")%string s;

    ToString.ToFunctionLines := @Bedrock2_ToFunctionLines;

    ToString.header := fun _ _ _ _ _ _ _ _ _ _ _ => [""; ToCString.prelude];

    ToString.footer := fun _ _ _ _ _ _ _ _ _ => [];

    (** No special handling for any functions *)
    ToString.strip_special_infos machine_wordsize infos := infos;

  |}.
