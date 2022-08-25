Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.HexString.
Require Crypto.Util.Strings.String.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.ParseArithmeticToTaps.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Strings.NamingConventions.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Strings.ParseDebugOptions.
Require Import Crypto.Util.DebugMonad.
Require Crypto.PushButtonSynthesis.SaturatedSolinas.
Require Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.PushButtonSynthesis.BaseConversion.
Require Crypto.PushButtonSynthesis.SolinasReduction.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Stringification.C.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Stringification.Rust.
Require Import Crypto.Stringification.Go.
Require Import Crypto.Stringification.Java.
Require Import Crypto.Stringification.JSON.
Require Import Crypto.Stringification.Zig.
Require Crypto.Util.Arg.
Import ListNotations. Local Open Scope Z_scope. Local Open Scope string_scope.

Import
  Stringification.Language.Compilers
  Stringification.C.Compilers.

Module ForExtraction.
  Definition parse_string_and {T} (parse_T : string -> option T) (s : string) : option (string * T)
    := option_map (@pair _ _ s) (parse_T s).
  Definition parse_Z (s : string) : option Z := parseZ_arith_strict s.
  Definition parse_N (s : string) : option N := parseN_arith_strict s.
  Definition parse_nat (s : string) : option nat := parsenat_arith_strict s.
  Definition parse_Q (s : string) : option Q := parseQ_arith_strict s.
  Definition parse_bool (s : string) : option bool
    := if string_dec s "true"
       then Some true
       else if string_dec s "false"
            then Some false
            else None.
  Definition parse_list_Z (s : string) : option (list Z)
    := (ls <- finalize (parse_list ParseArithmetic.parse_Qexpr) s;
          ls <-- List.map ParseArithmetic.eval_Qexpr_strict ls;
          ls <-- List.map ParseArithmetic.Q_to_Z_strict ls;
          Some ls).

  Definition parse_list_REG (s : string) : option (list REG)
    := finalize (parse_comma_list parse_REG) s.

  Definition parse_comma_list_Z (s : string) : option (list Z)
    := (ls <- finalize (parse_comma_list ParseArithmetic.parse_Qexpr) s;
          ls <-- List.map ParseArithmetic.eval_Qexpr_strict ls;
          ls <-- List.map ParseArithmetic.Q_to_Z_strict ls;
          Some ls).

  Definition parse_callee_saved_registers (s : string) : option assembly_callee_saved_registers_opt
    := finalize parse_assembly_callee_saved_registers_opt s.

  (* Workaround for lack of notation in 8.8 *)
  Local Notation "x =? y" := (if string_dec x y then true else false) : string_scope.

  Definition parse_n (n : string) : option MaybeLimbCount
    := match parse_nat n with
       | Some n => Some (NumLimbs n)
       | None
         => let idx1 := String.length "(auto" in
            let autov := substring 0 idx1 n in
            let numv := substring idx1 (String.length n) n in
            let numv := substring 0 (String.length numv - 1) numv in
            let lastch := substring (String.length n - 1) 1 n in
            if ((lastch =? ")") && (autov =? "(auto"))%string%bool
            then let numv := if (numv =? "")%string
                             then Some 0%nat
                             else parse_nat numv in
                 option_map Auto numv
            else None
       end.

  Definition parse_sc (s : string) : option (Z * list (Z * Z))
    := parseZ_arith_to_taps s.

  Definition parse_machine_wordsize (s : string) : option Z
    := parse_Z s.
  Definition parse_m (s : string) : option Z
    := parse_Z s.

  Definition parse_case_convention (s : string) : option capitalization_data
    := parse_capitalization_data_strict s.
  Definition valid_case_conventions : string
    := Eval compute in
        String.concat
          ", "
          (List.flat_map
             (fun '(_, ls)
              => match ls with
                 | [] => []
                 | [n] => [n]
                 | n :: ns
                   => [n ++ " (alternatively: " ++ String.concat ", " ns ++ ")"]
                 end%string)
             parse_capitalization_data_pre_list).

  Definition parse_src_n : string -> option nat := parse_nat.
  Definition parse_limbwidth : string -> option Q := parse_Q.
  Definition parse_max (s : string) : option (option Z)
    := option_map (@Some _) (parse_Z s).
  Definition parse_bounds_multiplier (s : option string) : string * option (option Q)
    := let s := Option.value s "" in
       (s,
        if string_dec s ""
        then Some None
        else option_map (@Some _) (parse_Q s)).
  Definition parse_dirbounds_multiplier (dir : string) (s : option string + list string) : string * (option Q + list string)
    := match s with
       | inl s
         => let '(s, q) := parse_bounds_multiplier s in
            (s,
             match q with
             | Some q => inl q
             | None => inr ["Could not parse '" ++ s ++ "' as a ℚ for --" ++ dir ++ "bounds-multiplier"]%string
             end)
       | inr opts
         => ("", inr ["Argument --" ++ dir ++ "bounds-multiplier can only be passed once; passed multiple times with values: " ++ String.concat ", " opts])
       end.

  Definition parse_bounds_list (s : option string) : string * option (option (list Z))
    := match s with
       | None => ("", Some None)
       | Some s
         => (s,
             option_map (@Some _) (parse_list_Z s))
       end.

  Definition parse_dirbounds (dir : string) (s : option string + list string) (use_bitwidth : bool) : string * (BaseConversion.bounds + list string)
    := match s with
       | inl s
         => let '(s, ls) := parse_bounds_list s in
            (s,
             match ls, use_bitwidth with
             | Some (Some ls), false => inl (BaseConversion.exactly ls)
             | Some None, false => inl BaseConversion.use_prime
             | Some None, true => inl BaseConversion.use_bitwidth
             | _, _
               => let err1 := match ls, use_bitwidth with
                              | Some _, true => ["Cannot pass both --use-bitwidth-" ++ dir ++ " and --" ++ dir ++ "bounds=" ++ s]%string
                              | _, _ => []
                              end in
                  let err2 := match ls with
                              | None => ["Could not parse " ++ dir ++ "bounds (" ++ s ++ ")"]%string
                              | _ => []
                              end in
                  inr (err1 ++ err2)%list
             end)
       | inr opts
         => ("",
             inr ((["Argument --" ++ dir ++ "bounds can only be passed once; passed multiple times with values: " ++ String.concat ", " opts]%string)
                    ++ if use_bitwidth
                       then ["Cannot pass both --use-bitwidth-" ++ dir ++ " and --" ++ dir ++ "bounds"]%string
                       else [])%list)
       end.

  Definition show_c : Show (list (Z * Z))
    := @show_list _ (@show_prod _ _ PowersOfTwo.show_Z Decimal.show_Z).

  Local Open Scope string_scope.

  (** TODO: Write a better quoter and maybe move this elsewhere *)
  (** https://mywiki.wooledge.org/BashGuide/SpecialCharacters *)
  (** We also quote the "/" character so that we don't change quoting behavior based on Windows vs Linux paths *)
  Definition quote (s : string) : string
    := if List.existsb (fun ch => List.existsb (fun badch => badch =? ch)%char
                                               [" "; "$"; "'"; """"; "\"; "#"; "="; "!"; ">"; "<"; "|"; ";"; "{"; "}"; "("; ")"; "["; "]"; "*"; "?"; "~"; "&"; "`"; "/"]%char)
                       (String.list_ascii_of_string s)
          || (String.length s =? 0)%nat
       then "'" ++ String.replace "'" "'""'""'" s ++ "'"
       else s.

  Definition known_debug_options_with_spec : list (string * string)
    := [("on-success", "In addition to printing the debug information when synthesis fails, also print it when synthesis succeeds.")
        ; ("rewriting", "Print the AST before and after each rewriting pass.")
    ].
  Definition known_debug_options : list string
    := Eval compute in List.map fst known_debug_options_with_spec.
  Definition special_debug_options : list (string * debug_option_kind)
    := [("all", all)
    ].
  (** This string gets parsed as the initial argument to --debug, to be updated by subsequent arguments *)
  Definition default_debug : string := "rewriting".

  Definition CollectErrors
             {machine_wordsize : machine_wordsize_opt}
             {output_language_api : ToString.OutputLanguageAPI}
             (res : list (synthesis_output_kind * string * Pipeline.M (list string)))
    : Pipeline.DebugM (((* normal *) list (list string)) * ((* asm output *) list (list string))) + (* error *) list (Pipeline.DebugM (list string))
    := (let header := hd "" (List.map (@snd _ _) (List.map (@fst _ _) res)) in
        let res :=
          List.fold_right
            (fun '(kind, name, res) rest
             => match Debug.eval_result res, rest with
                | ErrorT.Error err, rest
                  => let in_name := ("In " ++ name ++ ":") in
                     let cur :=
                       match show_lines err with
                       | [serr] => [in_name ++ " " ++ serr]
                       | serr => in_name::serr
                       end in
                     let rest := match rest with inl _ => nil | inr rest => rest end in
                     inr ((Debug.with_debug_info res (Debug.ret cur)) :: rest)
                | ErrorT.Success v, inr ls => inr ls
                | ErrorT.Success v, inl ls
                  => inl (Debug.copy_debug_info res;;
                          ls <- ls;
                          Debug.ret
                            (match kind, ls with
                             | normal_output  , (ls_normal, ls_asm)
                               => (v :: ls_normal, ls_asm)
                             | assembly_output, (ls_normal, ls_asm)
                               => (ls_normal, v :: ls_asm)
                             end))
                end)
            (inl (Debug.ret (nil, nil)))
            res in
        match res with
        | inl ls => inl ls
        | inr err => inr (Debug.ret [header]::err)
        end)%debugM.

  Class supported_languagesT := supported_languages : list (string * ToString.OutputLanguageAPI).

  (** N.B. The order matters, as the first element of the supported
      languages list is used as the default. *)
  Definition default_supported_languages : supported_languagesT
    := [("C", ToString.OutputCAPI)
        ; ("Rust", Rust.OutputRustAPI)
        ; ("Go", Go.OutputGoAPI)
        ; ("Java", Java.OutputJavaAPI)
        ; ("JSON", JSON.OutputJSONAPI)
        ; ("Zig", Zig.OutputZigAPI)].

  Local Notation anon_argT := (string * Arg.spec * Arg.doc)%type (only parsing).
  Local Notation named_argT := (list Arg.key * Arg.spec * Arg.doc)%type (only parsing).

  Definition curve_description_spec : anon_argT
    := ("curve_description",
        Arg.String,
        ["A string which will be prefixed to every function name generated"]).
  Definition lang_default {supported_languages : supported_languagesT}
    := List.hd ("C", ToString.OutputCAPI) supported_languages.
  Definition lang_spec {supported_languages : supported_languagesT} : named_argT
    := let supported_language_names := List.map (@fst _ _) supported_languages in
       ([Arg.long_key "lang"],
        Arg.CustomSymbol supported_languages,
        ["The output language code should be emitted in.  Defaults to " ++ List.hd "C" supported_language_names ++ " if no language is given.  Case-sensitive."]).
  Definition no_prefix_fiat_spec : named_argT
    := ([Arg.long_key "no-prefix-fiat"], Arg.Unit, ["Don't prefix functions with fiat_"]).
  Definition package_name_spec : named_argT
    := ([Arg.long_key "package-name"], Arg.String, ["The name of the package, for languages that support it."]).
  Definition class_name_spec : named_argT
    := ([Arg.long_key "class-name"], Arg.String, ["The name of the class, for languages that support it."]).
  Definition private_function_case_spec : named_argT
    := ([Arg.long_key "private-function-case"],
        Arg.Custom (parse_string_and parse_case_convention) "CONVENTION",
        ["The case convention for non-exported function names.  Default is to not adjust case, resulting in, roughly, snake_case."
         ; "Valid options are: " ++ valid_case_conventions ++ "."]).
  Definition public_function_case_spec : named_argT
    := ([Arg.long_key "public-function-case"],
        Arg.Custom (parse_string_and parse_case_convention) "CONVENTION",
        ["The case convention for exported function names.  Default is to not adjust case, resulting in, roughly, snake_case."
         ; "Valid options are: " ++ valid_case_conventions ++ "."]).
  Definition private_type_case_spec : named_argT
    := ([Arg.long_key "private-type-case"],
        Arg.Custom (parse_string_and parse_case_convention) "CONVENTION",
        ["The case convention for non-exported type names.  Default is to not adjust case, resulting in, roughly, snake_case."
         ; "Valid options are: " ++ valid_case_conventions ++ "."]).
  Definition public_type_case_spec : named_argT
    := ([Arg.long_key "public-type-case"],
        Arg.Custom (parse_string_and parse_case_convention) "CONVENTION",
        ["The case convention for exported type names.  Default is to not adjust case, resulting in, roughly, snake_case."
         ; "Valid options are: " ++ valid_case_conventions ++ "."]).
  Definition class_case_spec : named_argT
    := ([Arg.long_key "class-case"],
        Arg.Custom (parse_string_and parse_case_convention) "CONVENTION",
        ["The case convention for the default class name.  Only meaningful when the class name is inferred from curve_description, rather than given explicitly with --class-name."
         ; "Valid options are: " ++ valid_case_conventions ++ "."]).
  Definition package_case_spec : named_argT
    := ([Arg.long_key "package-case"],
        Arg.Custom (parse_string_and parse_case_convention) "CONVENTION",
        ["The case convention for the default package name.  Only meaningful when the package name is inferred from curve_description, rather than given explicitly with --package-name."
         ; "Valid options are: " ++ valid_case_conventions ++ "."]).
  Definition static_spec : named_argT
    := ([Arg.long_key "static"], Arg.Unit, ["Declare the functions as static, i.e., local to the file."]).
  Definition internal_static_spec : named_argT
    := ([Arg.long_key "internal-static"], Arg.Unit, ["Declare internal functions as static, i.e., local to the file."]).
  Definition inline_spec : named_argT
    := ([Arg.long_key "inline"], Arg.Unit, ["Declare all functions as inline."]).
  Definition inline_internal_spec : named_argT
    := ([Arg.long_key "inline-internal"], Arg.Unit, ["Declare internal functions as inline."]).
  Definition only_signed_spec : named_argT
    := ([Arg.long_key "only-signed"], Arg.Unit, ["Only allow signed integer types."]).
  Definition no_select_spec : named_argT
    := ([Arg.long_key "no-select"], Arg.Unit, ["Use expressions that don't require cmov."]).
  Definition no_wide_int_spec : named_argT
    := ([Arg.long_key "no-wide-int"], Arg.Unit, ["Don't use integers wider than the bitwidth."]).
  Definition widen_carry_to_bytes_spec : named_argT
    := ([Arg.long_key "widen-carry-to-bytes"], Arg.Unit, ["Always widen carry bit integer types the byte type, or to the full bitwidth if --widen-bytes is also passed."]).
  Definition widen_carry_spec : named_argT
    := ([Arg.long_key "widen-carry"], Arg.Unit, ["Widen carry bit integer types to either the byte type, or to the full bitwidth if --widen-bytes is also passed."]).
  Definition widen_bytes_spec : named_argT
    := ([Arg.long_key "widen-bytes"], Arg.Unit, ["Widen byte types to the full bitwidth."]).
  Definition split_multiret_spec : named_argT
    := ([Arg.long_key "split-multiret"], Arg.Unit, ["Don't allow instructions to return two results. This should always be set for bedrock2."]).
  Definition value_barrier_spec : named_argT
    := ([Arg.long_key "use-value-barrier"], Arg.Unit, ["Guard some expressions with an assembly barrier to prevent compilers from generating non-constant-time code for cmovznz."]).
  Definition no_primitives_spec : named_argT
    := ([Arg.long_key "no-primitives"], Arg.Unit, ["Suppress the generation of the bodies of primitive operations such as addcarryx, subborrowx, cmovznz, mulx, etc."]).
  Definition no_field_element_typedefs_spec : named_argT
    := ([Arg.long_key "no-field-element-typedefs"], Arg.Unit, ["Do not use type aliases for field elements based on bounds, Montgomery-domain vs not Montgomery-domain, etc."]).
  Definition emit_all_casts_spec : named_argT
    := ([Arg.long_key "emit-all-casts"], Arg.Unit, ["Rather than performing language-specific cast-adjustment, just emit all casts that are present in the intermediate representation, annotating all constructions."]).
  Definition relax_primitive_carry_to_bitwidth_spec : named_argT
    := ([Arg.long_key "relax-primitive-carry-to-bitwidth"],
        Arg.Custom (parse_string_and parse_comma_list_Z) "ℤ,ℤ,…",
        ["For any (comma-separated) bitwidths passed to this argument, use bitwidth-sized bounds rather than tighter bounds for the carry return value of primitives such as addcarryx and subborrowx."]).
  Definition cmovznz_by_mul_spec : named_argT
    := ([Arg.long_key "cmovznz-by-mul"], Arg.Unit, ["Use an alternative implementation of cmovznz using multiplication rather than bitwise-and with -1."]).
  Definition shiftr_avoid_uint1_spec : named_argT
    := ([Arg.long_key "shiftr-avoid-uint1"], Arg.Unit, ["Avoid uint1 types at the output of (>>) operations."]).
  Definition tight_bounds_multiplier_default := default_tight_upperbound_fraction.
  Definition tight_bounds_multiplier_spec : named_argT
    := ([Arg.long_key "tight-bounds-mul-by"],
        Arg.Custom (parse_string_and parse_Q) "ℚ",
        ["The (improper) fraction by which the (tight) bounds of each limb are scaled"]).
  Definition n_spec : anon_argT
    := ("n",
        Arg.Custom (parse_string_and parse_n) "an ℕ or the literal '(auto)' or '(autoN)' for a non-negative number N",
        ["The number of limbs, or the literal '(auto)' or '(autoN)' for a non-negative number N, to automatically guess the number of limbs"]).
  Definition sc_spec : anon_argT
    := ("s-c",
        Arg.Custom (parse_string_and parse_sc) "an integer expression",
        ["The prime, which must be expressed as a difference of a power of two and a small field element (e.g., '2^255 - 19', '2^448 - 2^224 - 1')"]).
  Definition m_spec : anon_argT
    := ("m",
        Arg.Custom (parse_string_and parse_m) "an integer expression",
        ["The prime (e.g., '2^434 - (2^216*3^137 - 1)')"]).
  Definition machine_wordsize_spec : anon_argT
    := ("machine_wordsize",
        Arg.Custom (parse_string_and parse_machine_wordsize) "an integer",
        ["The machine bitwidth (e.g., 32 or 64)"]).
  Definition src_n_spec : anon_argT
    := ("src_n",
        Arg.Custom (parse_string_and parse_src_n) "ℕ",
        ["The number of limbs in the input"]).
  Definition src_limbwidth_spec : anon_argT
    := ("src_limbwidth",
        Arg.Custom (parse_string_and parse_limbwidth) "ℕ",
        ["The limbwidth of the input field element"]).
  Definition dst_limbwidth_spec : anon_argT
    := ("dst_limbwidth",
        Arg.Custom (parse_string_and parse_limbwidth) "ℕ",
        ["The limbwidth of the field element to be returned"]).
  Definition use_bitwidth_in_spec : named_argT
    := ([Arg.long_key "use-bitwidth-in"],
        Arg.Unit,
        ["Instead of using an upper bound of s-1 on the input, use the maximum number that can be properly represented with the given base"]).
  Definition use_bitwidth_out_spec : named_argT
    := ([Arg.long_key "use-bitwidth-out"],
        Arg.Unit,
        ["Instead of using an upper bound of s-1 on the output, use the maximum number that can be properly represented with the given base"]).
  Definition default_inbounds_multiplier := 1.
  Definition inbounds_multiplier_spec : named_argT
    := ([Arg.long_key "inbounds-multiplier"],
        Arg.String,
        ["The (improper) fraction by which the bounds of each input limb are scaled (default: " ++ show default_inbounds_multiplier ++ ")"]).
  Definition default_outbounds_multiplier := 1.
  Definition outbounds_multiplier_spec : named_argT
    := ([Arg.long_key "outbounds-multiplier"],
        Arg.String,
        ["The (improper) fraction by which the bounds of each output limb are scaled (default: " ++ show default_outbounds_multiplier ++ ")"]).
  Definition inbounds_spec : named_argT
    := ([Arg.long_key "inbounds"],
        Arg.String,
        ["A semicolon-separated, square-bracked-surrounded list of integer expressions describing the input bounds.  Incompatible with --use-bitwidth-in."]).
  Definition outbounds_spec : named_argT
    := ([Arg.long_key "outbounds"],
        Arg.String,
        ["A semicolon-separated, square-bracked-surrounded list of integer expressions describing the output bounds.  Incompatible with --use-bitwidth-out."]).
  Definition function_to_synthesize_spec (valid_names : string) : anon_argT
    := ("function_to_synthesize",
        Arg.String,
        ["A space-separated list of functions that should be synthesized.  If no functions are given, all functions are synthesized."
         ; "Valid options are " ++ valid_names ++ "."]).
  Definition hint_file_spec : named_argT
    := ([Arg.long_key "hints-file"],
        Arg.String,
        ["An assembly file to be read for hinting the synthesis process.  Use - for stdin.  To check multiple files against the same synthesized operation(s), pass this argument multiple times."]).
  Definition output_file_spec : named_argT
    := ([Arg.long_key "output"; Arg.short_key "o"],
        Arg.String,
        ["The name of the file to write output to.  Use - for stdout.  (default: -)"]).
  Definition asm_output_spec : named_argT
    := ([Arg.long_key "output-asm"],
        Arg.String,
        ["The name of the file to write generated assembly to.  Use - for stdout.  (default: -)"]).
  Definition asm_reg_spec : named_argT
    := ([Arg.long_key "asm-reg"],
        Arg.Custom (parse_string_and parse_list_REG) "REG",
        ["A comma-separated list of registers to use for calling conventions.  Only relevant when --hints-file is specified."
         ; "Defaults to the System V AMD64 ABI of " ++ String.concat "," (List.map show default_assembly_calling_registers) ++ ".  Note that registers are first used for outputs and then inputs."]).
  Definition asm_callee_saved_registers_spec : named_argT
    := ([Arg.long_key "asm-callee-saved-registers"],
         Arg.Custom (parse_string_and parse_callee_saved_registers) "REG",
         ["Either '" ++ show System_V_AMD64 ++ "' (indicating " ++ String.concat "," (List.map show system_v_amd64_assembly_callee_saved_registers) ++ "), '" ++ show Microsoft_x64 ++ "' (indicating " ++ String.concat "," (List.map show microsoft_x64_assembly_callee_saved_registers) ++ "), or a comma-separated list of registers which are callee-saved / non-volatile.  Only relevant when --hints-file is specified."
          ; "Defaults to " ++ show default_assembly_callee_saved_registers ++ "."]).
  Definition asm_stack_size_spec : named_argT
    := ([Arg.long_key "asm-stack-size"],
        Arg.Custom (parse_string_and parse_N) "ℕ",
        ["The number of bytes of stack.  Only relevant when --hints-file is specified.  Defaults to " ++ show (extra_assembly_stack_size:N) ++ " plus the maximum statically knowable increase to `rsp` (via `push`, `pop`, `sub`, `add`, and `lea` instructions) the code."]).
  Definition no_error_on_unused_asm_functions_spec : named_argT
    := ([Arg.long_key "no-error-on-unused-asm-functions"],
        Arg.Unit,
        ["Don't error if there are global labels in the hints-file which are not requested functions."]).
  Definition asm_input_first_spec : named_argT
    := ([Arg.long_key "asm-input-first"],
        Arg.Unit,
        ["By default, output pointers are assumed to come before input arguments in the C code the assembly hints are based on.  This flag reverses that convention."]).
  Definition asm_reg_rtl_spec : named_argT
    := ([Arg.long_key "asm-reg-rtl"],
        Arg.Unit,
        ["By default, registers are assumed to be assigned to function arguments from left to right in the hints file.  This flag reverses that convention to be right-to-left.  Note that this flag interacts with --asm-input-first, which determines whether the output pointers are to the left or to the right of the input arguments."]).
  Definition asm_error_on_unique_names_mismatch_spec : named_argT
    := ([Arg.long_key "asm-error-on-unique-name-mismatch"],
        Arg.Unit,
        ["By default, when there's only one assembly function in a --hints-file and only one function requested to be synthesized, the name of the assembly function is ignored.  Passing this flag disables this behavior, raising an error if the names mismatch regardless of whether there are multiple functions or just one."]).
  Definition doc_text_before_function_name_spec : named_argT
    := ([Arg.long_key "doc-text-before-function-name"],
        Arg.String,
        ["Documentation Option: A custom string to insert before the function name in each docstring.  Default: " ++ default_text_before_function_name]).
  Definition doc_text_before_type_name_spec : named_argT
    := ([Arg.long_key "doc-text-before-type-name"],
        Arg.String,
        ["Documentation Option: A custom string to insert before the type name in each docstring.  Default: " ++ default_text_before_type_name]).
  Definition doc_newline_before_package_declaration_spec : named_argT
    := ([Arg.long_key "doc-newline-before-package-declaration"],
        Arg.Unit,
        ["Documentation Option: For languages that emit package declarations, add an extra newline before the declaration.  Primarily useful to detach the header from the Go package."]).
  Definition doc_newline_in_typedef_bounds_spec : named_argT
    := ([Arg.long_key "doc-newline-in-typedef-bounds"],
        Arg.Unit,
        ["Documentation Option: When emitting the documentation comment for typedefs, insert a newline between ""Bounds:"" and the bounds rather than a space."]).
  Definition doc_prepend_header_raw_spec : named_argT
    := ([Arg.long_key "doc-prepend-header-raw"],
        Arg.String,
        ["Documentation Option: Prepend a line before the documentation header at the top of the file.  This argument can be passed multiple times to insert multiple lines."]).
  Definition doc_prepend_header_spec : named_argT
    := ([Arg.long_key "doc-prepend-header"],
        Arg.String,
        ["Documentation Option: Prepend a line at the beginning of the documentation header at the top of the file.  This argument can be passed multiple times to insert multiple lines.  Lines will be automatically commented."]).
  Definition debug_spec : named_argT
    := let len := List.fold_right Nat.max 0%nat (List.map String.length (known_debug_options ++ List.map fst special_debug_options)) in
       let fill s := (s ++ String.repeat " " (len - String.length s))%string in
       ([Arg.long_key "debug"; Arg.short_key "d"],
         Arg.String,
         (["A comma-separated list of debug options to turn on.  Use - to disable an option.  Default debug options: " ++ (if default_debug =? "" then "(none)" else default_debug)
           ; "Valid debug options:"]%string)
           ++ (List.flat_map
                 (fun '(opt, k)
                  => match k with
                     | all => ["- " ++ fill opt ++ String.Tab ++ "Turn all debugging on"]
                     | alias _ => []
                     end)%string
                 special_debug_options)
           ++ (List.map
                 (fun '(opt, descr) => "- " ++ fill opt ++ String.Tab ++ descr)%string
                 known_debug_options_with_spec)
           ++ (List.flat_map
                 (fun '(opt, k)
                  => match k with
                     | all => []
                     | alias ls => ["- " ++ fill opt ++ String.Tab ++ "an alias for " ++ String.concat "," ls]
                     end)%string
                 special_debug_options))%list.

  Definition collapse_list_default {A} (default : A) (ls : list A)
    := List.hd default (List.rev ls).

  Definition join_errors {A B} (x : A + list string) (y : B + list string) : (A * B) + list string
    := match x, y with
       | inr errs1, inr errs2 => inr (errs1 ++ errs2)%list
       | inr err, inl _ | inl _, inr err => inr err
       | inl x, inl y => inl (x, y)
       end.

  (** We define a class for holding the various options we might pass to [Synthesize] *)
  (** We split up the ones we can directly parse and the ones we have to process *)
  Class ParsedSynthesizeOptions :=
    {
      (** Is the code static / private *)
      static :> static_opt
      (** Is the internal code static / private *)
      ; internal_static :> internal_static_opt
      (** Is the code inlined *)
      ; inline :> inline_opt
      (** Is the internal code inlined *)
      ; inline_internal :> inline_internal_opt
      (** Should we only use signed integers *)
      ; only_signed :> only_signed_opt
      (** Should we emit expressions requiring cmov *)
      ; no_select :> no_select_opt
      (** Should we emit primitive operations *)
      ; emit_primitives :> emit_primitives_opt
      (** Various output options including: *)
      (** Should we skip emitting typedefs for field elements *)
      (** Should we relax the bounds on the return carry type of sbb/adc operations? *)
      ; output_options :> output_options_opt
      (** Should we use the alternate implementation of cmovznz *)
      ; use_mul_for_cmovznz :> use_mul_for_cmovznz_opt
      (** Various abstract interpretation options *)
      (** Should we avoid uint1 at the output of shiftr *)
      ; abstract_interpretation_options :> AbstractInterpretation.Options
      (** Should we split apart oversized operations? *)
      ; should_split_mul :> should_split_mul_opt
      (** Should we split apart multi-return operations? *)
      ; should_split_multiret :> should_split_multiret_opt
      (** Should we remove use of value_barrier? *)
      ; unfold_value_barrier :> unfold_value_barrier_opt
      (** Should we widen the carry to the full bitwidth? *)
      ; widen_carry :> widen_carry_opt
      (** Should we widen the byte type to the full bitwidth? *)
      ; widen_bytes :> widen_bytes_opt
      (** Should we ignore function-name mismatch errors when there's only one assembly function and only one actual function requested? *)
      ; ignore_unique_asm_names :> ignore_unique_asm_names_opt
      (** What method should we use for rewriting? *)
      ; low_level_rewriter_method :> low_level_rewriter_method_opt
        := default_low_level_rewriter_method
      (** What's the bitwidth? *)
      ; machine_wordsize :> machine_wordsize_opt
      (** What's the package name *)
      ; internal_package_name :> package_name_opt
      (** What's the class name *)
      ; internal_class_name :> class_name_opt
      (** What's are the naming conventions to use? *)
      ; language_naming_conventions :> language_naming_conventions_opt
      (** Documentation options *)
      ; documentation_options :> documentation_options_opt
      (** assembly convention options *)
      ; assembly_conventions :> assembly_conventions_opt
      (** error if there are un-requested assembly functions *)
      ; error_on_unused_assembly_functions :> error_on_unused_assembly_functions_opt
      (** don't prepend fiat to prefix *)
      ; no_prefix_fiat : bool
      (** Extra lines before the documentation header *)
      ; before_header_lines : list string
      (** Extra lines at the beginning of the documentation header *)
      ; extra_early_header_lines : list string
      (** Debug rewriting *)
      ; debug_rewriting :> debug_rewriting_opt
      (** Print debug info on success too *)
      ; debug_on_success : bool
    }.
  Class SynthesizeOptions :=
    {
      parsed_synthesize_options :> ParsedSynthesizeOptions
      (** Lines of assembly hints *)
      ; assembly_hints_lines :> assembly_hints_lines_opt
    }.

  (** We define a class for holding the various options about file interaction that we don't pass to [Synthesize] *)
  Class IODriverOptions :=
    {
      (** The name of the file holding assembly hints *)
      hint_file_names : list string
      (** The name of the file to output to *)
      ; output_file_name : string
      (** The name of the file to output assembly to *)
      ; asm_output_file_name : string
    }.

  Fixpoint with_read_concat_asm_files_cps
           {A}
           (with_read_file : string (* fname *) -> (list string -> A) -> A)
           (hint_file_names : list string)
    : (assembly_hints_lines_opt -> A) -> A
    := match hint_file_names with
       | nil => fun k => k []
       | fname :: fnames
         => fun k
            => with_read_file
                 fname
                 (fun lines
                  => with_read_concat_asm_files_cps
                       with_read_file
                       fnames
                       (fun rest => k ((fname, lines) :: rest)))
       end.

  Definition common_optional_options {supported_languages : supported_languagesT}
    := [lang_spec
        ; package_name_spec
        ; class_name_spec
        ; package_case_spec
        ; class_case_spec
        ; private_function_case_spec
        ; public_function_case_spec
        ; private_type_case_spec
        ; public_type_case_spec
        ; no_prefix_fiat_spec
        ; static_spec
        ; internal_static_spec
        ; inline_spec
        ; inline_internal_spec
        ; no_wide_int_spec
        ; widen_carry_spec
        ; widen_bytes_spec
        ; no_select_spec
        ; split_multiret_spec
        ; value_barrier_spec
        ; no_primitives_spec
        ; no_field_element_typedefs_spec
        ; emit_all_casts_spec
        ; relax_primitive_carry_to_bitwidth_spec
        ; cmovznz_by_mul_spec
        ; shiftr_avoid_uint1_spec
        ; only_signed_spec
        ; hint_file_spec
        ; output_file_spec
        ; asm_output_spec
        ; asm_reg_spec
        ; asm_callee_saved_registers_spec
        ; asm_stack_size_spec
        ; no_error_on_unused_asm_functions_spec
        ; asm_input_first_spec
        ; asm_reg_rtl_spec
        ; asm_error_on_unique_names_mismatch_spec
        ; doc_text_before_function_name_spec
        ; doc_text_before_type_name_spec
        ; doc_newline_before_package_declaration_spec
        ; doc_newline_in_typedef_bounds_spec
        ; doc_prepend_header_raw_spec
        ; doc_prepend_header_spec
        ; debug_spec
       ].

  (* We follow the standard convention of giving precedence to the final option passed *)
  Definition choose_one_of_many {A} (args : list A) : option A
    := List.nth_error (List.rev args) 0.

  Definition parse_common_optional_options
             {supported_languages : supported_languagesT}
             {machine_wordsizev : machine_wordsize_opt}
             (data : Arg.keyed_spec_list_data common_optional_options)
    : (IODriverOptions * ParsedSynthesizeOptions * ToString.OutputLanguageAPI) + list string
    := let '(langv
             , package_namev
             , class_namev
             , package_casev
             , class_casev
             , private_function_casev
             , public_function_casev
             , private_type_casev
             , public_type_casev
             , no_prefix_fiatv
             , staticv
             , internal_staticv
             , inlinev
             , inline_internalv
             , no_wide_intv
             , widen_carryv
             , widen_bytesv
             , no_selectv
             , split_multiretv
             , value_barrierv
             , no_primitivesv
             , no_field_element_typedefsv
             , emit_all_castsv
             , relax_primitive_carry_to_bitwidthv
             , cmovznz_by_mulv
             , shiftr_avoid_uint1v
             , only_signedv
             , hint_file_namesv
             , output_file_namev
             , asm_output_file_namev
             , asm_regv
             , asm_callee_saved_registersv
             , asm_stack_sizev
             , no_error_on_unused_asm_functionsv
             , asm_input_firstv
             , asm_reg_rtlv
             , asm_error_on_unique_names_mismatchv
             , doc_text_before_function_namev
             , doc_text_before_type_namev
             , doc_newline_before_package_declarationv
             , doc_newline_in_typedef_boundsv
             , doc_prepend_header_rawv
             , doc_prepend_headerv
             , debugv
            ) := data in
       let debug_to_bool x := bool_of_full_debug_status x false in
       let to_bool ls := (0 <? List.length ls)%nat in
       let to_string_list ls := List.map (@snd _ _) ls in
       let to_N_list ls := List.map (@snd _ _) (List.map (@snd _ _) ls) in
       let to_Z_flat_list ls := List.flat_map (@snd _ _) (List.map (@snd _ _) ls) in
       let to_reg_list ls := match List.map (@snd _ _) (List.map (@snd _ _) ls) with
                             | nil => None
                             | ls => Some (List.concat ls)
                             end in
       let to_assembly_callee_saved_registers_opt ls := choose_one_of_many (List.map (fun '(_, (_, v)) => v) ls) in
       let to_assembly_callee_saved_registers_default ls default := Option.value (to_assembly_callee_saved_registers_opt ls) default in
       let to_N_opt ls := choose_one_of_many (to_N_list ls) in
       let to_N_default ls default := Option.value (to_N_opt ls) default in
       let to_string_opt ls := choose_one_of_many (to_string_list ls) in
       let to_string_default ls default := Option.value (to_string_opt ls) default in
       let to_capitalization_data_opt ls := choose_one_of_many (List.map (fun '(_, (_, v)) => v) ls) in
       let to_capitalization_convention_opt ls
           := option_map (fun d => {| capitalization_convention_data := d ; only_lower_first_letters := true |})
                         (to_capitalization_data_opt ls) in
       let '(_, unknown_debug_options, (debug_on_successv, debug_rewritingv)) := parse_debug_opts special_debug_options known_debug_options (default_debug :: List.map snd debugv) in
       let res
           := ({|
                  hint_file_names := to_string_list hint_file_namesv
                  ; output_file_name := to_string_default output_file_namev "-"
                  ; asm_output_file_name := to_string_default asm_output_file_namev "-"
                |},
               {| static := to_bool staticv
                  ; internal_static := to_bool internal_staticv
                  ; inline := to_bool inlinev
                  ; inline_internal := to_bool inline_internalv
                  ; internal_class_name := to_string_opt class_namev
                  ; internal_package_name := to_string_opt package_namev
                  ; language_naming_conventions
                    := {| public_function_naming_convention := to_capitalization_convention_opt public_function_casev
                          ; private_function_naming_convention := to_capitalization_convention_opt private_function_casev
                          ; public_type_naming_convention := to_capitalization_convention_opt public_type_casev
                          ; private_type_naming_convention := to_capitalization_convention_opt private_type_casev
                          ; variable_naming_convention := None
                          ; package_naming_convention := to_capitalization_convention_opt package_casev
                          ; class_naming_convention := to_capitalization_convention_opt class_casev
                       |}
                  ; no_prefix_fiat := to_bool no_prefix_fiatv
                  ; widen_carry := to_bool widen_carryv
                  ; widen_bytes := to_bool widen_bytesv
                  ; no_select := to_bool no_selectv
                  ; only_signed := to_bool only_signedv
                  ; should_split_mul := to_bool no_wide_intv
                  ; should_split_multiret := to_bool split_multiretv
                  ; unfold_value_barrier := negb (to_bool value_barrierv)
                  ; use_mul_for_cmovznz := to_bool cmovznz_by_mulv
                  ; abstract_interpretation_options :=
                      {| AbstractInterpretation.shiftr_avoid_uint1 := to_bool shiftr_avoid_uint1v
                      |}
                  ; emit_primitives := negb (to_bool no_primitivesv)
                  ; output_options :=
                      {| skip_typedefs_ := to_bool no_field_element_typedefsv
                      ; relax_adc_sbb_return_carry_to_bitwidth_ := to_Z_flat_list relax_primitive_carry_to_bitwidthv
                      ; language_specific_cast_adjustment_ := negb (to_bool emit_all_castsv)
                      |}
                  ; assembly_conventions :=
                    {| assembly_calling_registers_ := to_reg_list asm_regv
                    ; assembly_callee_saved_registers_ := to_assembly_callee_saved_registers_default asm_callee_saved_registersv default_assembly_callee_saved_registers
                    ; assembly_stack_size_ := to_N_opt asm_stack_sizev
                    ; assembly_output_first_ := negb (to_bool asm_input_firstv)
                    ; assembly_argument_registers_left_to_right_ := negb (to_bool asm_reg_rtlv)
                    |}
                  ; ignore_unique_asm_names := negb (to_bool asm_error_on_unique_names_mismatchv)
                  ; error_on_unused_assembly_functions := negb (to_bool no_error_on_unused_asm_functionsv)
                  ; documentation_options
                    := {| text_before_function_name_opt := to_string_opt doc_text_before_function_namev
                          ; text_before_type_name_opt := to_string_opt doc_text_before_type_namev
                          ; newline_before_package_declaration := to_bool doc_newline_before_package_declarationv
                          ; newline_in_typedef_bounds := to_bool doc_newline_in_typedef_boundsv
                       |}
                  ; before_header_lines := to_string_list doc_prepend_header_rawv
                  ; extra_early_header_lines := to_string_list doc_prepend_headerv
                  ; debug_rewriting := debug_to_bool debug_rewritingv
                  ; debug_on_success := debug_to_bool debug_on_successv
               |},
               snd (List.hd lang_default langv)) in
       match langv, unknown_debug_options with
       | ([] | [_]), [] => inl res
       | _ :: _ :: _, _ => inr ["Only one language specification with --lang is allowed; multiple languages were requested: " ++ String.concat ", " (List.map (@fst _ _) langv)]
       | _, _ :: _
         => inr ["Unrecognized debug option" ++ (if (1 <? List.length unknown_debug_options)%nat then "s" else "") ++ ": " ++ String.concat ", " (List.map fst unknown_debug_options)]
       end.

  (** We define a class for the various operations that are specific to a pipeline *)
  Class PipelineAPI :=
    {
      (** The spec of curve-specific command line arguments *)
      spec : Arg.arg_spec;
      (** Type of arguments parsed from the command line *)
      ParsedArgsT : Type;
      (** Type of (unparsed) arguments remembered from the command line *)
      StringArgsT : Type;
      ArgsT := (StringArgsT * ParsedArgsT)%type;

      (** Takes in args parsed via the spec and post-parses
          curve-specific arguments, returning either [inl value] or
          [inr errors] *)
      parse_args : forall {synthesize_opts : SynthesizeOptions}, Arg.arg_spec_results spec -> ArgsT + list string;

      (** Renders a header at the top displaying the command line
          arguments.  Will be wrapped in a comment block *)
      show_lines_args : ArgsT -> list string;

      (** The Synthesize function from the pipeline *)
      (** N.B. [comment_header] will be passed in *without* wrapping
          it in a comment block first *)
      Synthesize : forall
          {output_language_api : ToString.OutputLanguageAPI}
          {synthesize_opts : SynthesizeOptions}
          (args : ParsedArgsT) (comment_header : list string) (function_name_prefix : string),
          list (synthesis_output_kind * string * Pipeline.M (list string))
    }.

  (** API for performing IO *)
  Class IODriverAPI {A} :=
    {
      error : list string -> A
      ; ret : unit -> A
      ; with_read_stdin : (list string -> A) -> A
      ; write_stdout_then : list string (* lines, to be joined with "" *) -> (unit -> A) -> A
      ; write_stderr_then : list string (* lines, to be joined with "" *) -> (unit -> A) -> A
      ; with_read_file : string (* fname *) -> (list string -> A) -> A
      ; write_file_then : string (* fname *) -> list string (* lines, to be joined with "" *) -> (unit -> A) -> A
    }.
  Global Arguments IODriverAPI : clear implicits.

  Module Export Notations.
    Bind Scope list_scope with supported_languagesT.
  End Notations.

  Module Parameterized.
    Section __.
      Context {api : PipelineAPI}.

      Definition PipelineLines
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (str_machine_wordsize : string)
                 (args : ArgsT)
        : list (synthesis_output_kind * string * Pipeline.M (list string))
        := let prefix := ((if no_prefix_fiat then "" else "fiat_")
                            ++ (if (curve_description =? "") then "" else (curve_description ++ "_")))%string in
           let header :=
               ((extra_early_header_lines
                   ++ ["Autogenerated: " ++ invocation
                       ; match (curve_description =? ""), internal_package_name, internal_class_name with
                         | false, _, _
                         | _, (None | Some ""), (None | Some "")
                           => "curve description: " ++ curve_description
                         | _, Some pkg, _
                           => "curve description (via package name): " ++ pkg
                         | _, _, Some cls
                           => "curve description (via class name): " ++ cls
                         end
                       ; "machine_wordsize = " ++ show (machine_wordsize:Z) ++ " (from """ ++ str_machine_wordsize ++ """)"]%string)
                  ++ show_lines_args args)%list in
           Synthesize (snd args) header prefix.

      Local Notation debug_to_lines v
        := (List.flat_map (fun f => String.NewLine :: f tt) (Debug.get_debug_info v)).

      Definition ProcessedLines
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (str_machine_wordsize : string)
                 (args : ArgsT)
        : Pipeline.DebugM ((* normal *) list string * (* asm *) list string) + list string
        := match CollectErrors (PipelineLines invocation curve_description str_machine_wordsize args) with
           | inl ls
             => let '(ls_normal, ls_asm) := Debug.eval_result ls in
                let before_header := List.map (fun s => s ++ String.NewLine) before_header_lines in
                let postprocess_lines ls
                    := String.strip_trailing_newlines
                         (List.flat_map (fun s => ((List.map (fun s => s ++ String.NewLine) (List.map String.strip_trailing_spaces s))%string)
                                                    ++ [String.NewLine])
                                        ls)%list in
                inl
                  (Debug.copy_debug_info ls;;
                   Debug.ret (before_header ++ postprocess_lines ls_normal, postprocess_lines ls_asm)%list)
           | inr nil => inr nil
           | inr (l :: ls)
             => let flatten_debug_info (ls : DebugM (list string))
                  := let dbg := debug_to_lines ls in
                     let ls := Debug.eval_result ls in
                     (dbg ++ ls)%list in
                inr ((flatten_debug_info l)
                       ++ (List.flat_map
                             (fun e => String.NewLine :: flatten_debug_info e)
                             ls))%list
           end%debugM.

      Definition Pipeline
                 {A}
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (str_machine_wordsize : string)
                 (args : ArgsT)
                 (success : list string (* stderr *) * list string (* normal lines *) * list string (* asm lines *) -> A)
                 (error : list string -> A)
        : A
        := match ProcessedLines invocation curve_description str_machine_wordsize args with
           | inl s => let stderr := if debug_on_success
                                    then debug_to_lines s
                                    else [] in
                      let '(normal_ls, asm_ls) := Debug.eval_result s in
                      success (stderr, normal_ls, asm_ls)
           | inr s => error s
           end.

      Definition PipelineMain
                 {supported_languages : supported_languagesT}
                 {A}
                 {io_driver : IODriverAPI A}
                 (argv : list string)
        : A
        := let with_read_file fname
               := if (fname =? "-")%string then with_read_stdin else with_read_file fname in
           let write_file_then fname
               := if (fname =? "-")%string then write_stdout_then else write_file_then fname in
           let invocation := String.concat " " (List.map quote argv) in
           let full_spec
               := {| Arg.named_args := common_optional_options ++ spec.(Arg.named_args)
                     ; Arg.anon_args := curve_description_spec :: machine_wordsize_spec :: spec.(Arg.anon_args)
                     ; Arg.anon_opt_args := spec.(Arg.anon_opt_args)
                     ; Arg.anon_opt_repeated_arg := spec.(Arg.anon_opt_repeated_arg) |} in
           match Arg.parse_argv argv full_spec with
           | ErrorT.Success (named_data, anon_data, anon_opt_data, anon_opt_repeated_data)
             => let '(common_named_data, named_data) := Arg.split_type_of_list' (ls1:=List.map _ common_optional_options) named_data in
                let '((curve_description, (str_machine_wordsize, machine_wordsize)), anon_data) := Arg.split_type_of_list' (ls1:=[_;_]) anon_data in
                let machine_wordsize : machine_wordsize_opt := machine_wordsize in
                match parse_common_optional_options common_named_data with
                | inl (io_driver_opts, opts, output_language_api)
                  => with_read_concat_asm_files_cps
                       with_read_file
                       hint_file_names
                       (fun assembly_hints_linesv
                        => let success :=
                               fun '(stderr, normal_lines, asm_lines)
                               => write_stderr_then
                                    stderr
                                    (fun 'tt
                                     => write_file_then
                                          output_file_name
                                          normal_lines
                                          (fun 'tt
                                           => match asm_lines, assembly_hints_linesv with
                                              | nil, [] => ret tt
                                              | _, _ => write_file_then
                                                          asm_output_file_name
                                                          asm_lines
                                                          ret
                                              end)) in
                           let opts := {|
                                 parsed_synthesize_options := opts
                                 ; assembly_hints_lines := assembly_hints_linesv
                               |} in
                           match parse_args (named_data, anon_data, anon_opt_data, anon_opt_repeated_data) with
                           | inl args
                             => Pipeline invocation curve_description str_machine_wordsize args success error
                           | inr errs => error errs
                           end)
                | inr errs => error errs
                end
           | ErrorT.Error err
             => let display := Arg.show_list_parse_error full_spec err in
                if Arg.is_real_error err
                then error display
                else (* just a requested help/usage message *)
                  write_stdout_then
                    (List.map (fun s => s ++ String.NewLine)%string display)
                    ret
           end.
    End __.
  End Parameterized.

  Module UnsaturatedSolinas.
    Local Instance api : PipelineAPI
      := {
          spec :=
            {| Arg.named_args := [tight_bounds_multiplier_spec]
               ; Arg.anon_args := [n_spec; sc_spec]
               ; Arg.anon_opt_args := []
               ; Arg.anon_opt_repeated_arg := Some (function_to_synthesize_spec UnsaturatedSolinas.valid_names) |};

          parse_args opts args
          := let '(tight_bounds_multiplier, ((str_n, n), (str_sc, (s, c))), tt, requests) := args in
             let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
             let '(str_tight_bounds_multiplier, tight_bounds_multiplier) := collapse_list_default ("", tight_bounds_multiplier_default) (List.map (@snd _ _) tight_bounds_multiplier) in
             let tight_bounds_multiplier : tight_upperbound_fraction_opt := tight_bounds_multiplier in
             match get_num_limbs s c machine_wordsize n, n with
             | None, NumLimbs n => inr ["Internal error: get_num_limbs (on (" ++ PowersOfTwo.show_Z s ++ ", " ++ show_c c ++ ", " ++ show (machine_wordsize:Z) ++ ", " ++ show n ++ ")) returned None even though the argument was NumLimbs"]
             | None, Auto idx => inr ["Invalid index " ++ show idx ++ " when guessing the number of limbs for s-c = " ++ PowersOfTwo.show_Z s ++ " - " ++ show_c c ++ "; valid indices must index into the list " ++ show (get_possible_limbs s c machine_wordsize) ++ "."]
             | Some n, _
               => inl
                    ((str_n, str_sc, str_tight_bounds_multiplier, show_requests),
                     (n, s, c, tight_bounds_multiplier, requests))
             end;

          show_lines_args :=
            fun '((str_n, str_sc, str_tight_bounds_multiplier, show_requests),
                  (n, s, c, tight_bounds_multiplier, requests))
            => ["requested operations: " ++ show_requests;
               "n = " ++ show n ++ " (from """ ++ str_n ++ """)";
               "s-c = " ++ PowersOfTwo.show_Z s ++ " - " ++ show_c c ++ " (from """ ++ str_sc ++ """)";
               "tight_bounds_multiplier = " ++ show (tight_bounds_multiplier:Q) ++ " (from """ ++ str_tight_bounds_multiplier ++ """)"]%string;

          Synthesize
          := fun _ opts '(n, s, c, tight_bounds_multiplier, requests) comment_header prefix
             => UnsaturatedSolinas.Synthesize n s c machine_wordsize comment_header prefix requests;
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               {io_driver : IODriverAPI A}
               (argv : list string)
      : A
      := Parameterized.PipelineMain argv.
  End UnsaturatedSolinas.

  Module WordByWordMontgomery.
    Local Instance api : PipelineAPI
      := {
          spec :=
            {| Arg.named_args := []
               ; Arg.anon_args := [m_spec]
               ; Arg.anon_opt_args := []
               ; Arg.anon_opt_repeated_arg := Some (function_to_synthesize_spec WordByWordMontgomery.valid_names) |};

          parse_args opts args
          := let '(tt, (str_m, m), tt, requests) := args in
             let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
             inl ((str_m, show_requests),
                  (m, requests));

          show_lines_args :=
            fun '((str_m, show_requests),
                  (m, requests))
            => ["requested operations: " ++ show_requests;
               "m = " ++ Hex.show_Z m ++ " (from """ ++ str_m ++ """)";
               "                                                                  ";
               "NOTE: In addition to the bounds specified above each function, all";
               "  functions synthesized for this Montgomery arithmetic require the";
               "  input to be strictly less than the prime modulus (m), and also  ";
               "  require the input to be in the unique saturated representation. ";
               "  All functions also ensure that these two properties are true of ";
               "  return values.                                                  "];

          Synthesize
          := fun _ opts '(m, requests) comment_header prefix
             => WordByWordMontgomery.Synthesize m machine_wordsize comment_header prefix requests
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               {io_driver : IODriverAPI A}
               (argv : list string)
      : A
      := Parameterized.PipelineMain argv.
  End WordByWordMontgomery.

  Module SaturatedSolinas.
    Local Instance api : PipelineAPI
      := {
          spec :=
            {| Arg.named_args := []
               ; Arg.anon_args := [sc_spec]
               ; Arg.anon_opt_args := []
               ; Arg.anon_opt_repeated_arg := Some (function_to_synthesize_spec SaturatedSolinas.valid_names) |};

          parse_args opts args
          := let '(tt, (str_sc, (s, c)), tt, requests) := args in
             let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
             inl ((str_sc, show_requests),
                  (s, c, requests));

          show_lines_args :=
            fun '((str_sc, show_requests),
                  (s, c, requests))
            => ["requested operations: " ++ show_requests;
               "s-c = " ++ PowersOfTwo.show_Z s ++ " - " ++ show_c c ++ " (from """ ++ str_sc ++ """)"];

          Synthesize
          := fun _ opts '(s, c, requests) comment_header prefix
             => SaturatedSolinas.Synthesize s c machine_wordsize comment_header prefix requests
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               {io_driver : IODriverAPI A}
               (argv : list string)
      : A
      := Parameterized.PipelineMain argv.
  End SaturatedSolinas.

  Module SolinasReduction.
    Local Instance api : PipelineAPI
      := {
        spec :=
        {| Arg.named_args := []
        ; Arg.anon_args := [sc_spec]
        ; Arg.anon_opt_args := []
        ; Arg.anon_opt_repeated_arg := Some (function_to_synthesize_spec SolinasReduction.valid_names) |};

        parse_args opts args
        := let '(tt, (str_sc, (s, c)), tt, requests) := args in
           let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
           inl ((str_sc, show_requests),
                 (s, c, requests));

        show_lines_args :=
        fun '((str_sc, show_requests),
             (s, c, requests))
        => ["requested operations: " ++ show_requests;
           "s-c = " ++ PowersOfTwo.show_Z s ++ " - " ++ show_c c ++ " (from """ ++ str_sc ++ """)"];

        Synthesize
        := fun _ opts '(s, c, requests) comment_header prefix
           => SolinasReduction.Synthesize s c machine_wordsize comment_header prefix requests
      }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               {io_driver : IODriverAPI A}
               (argv : list string)
      : A
      := Parameterized.PipelineMain argv.
  End SolinasReduction.

  Module BaseConversion.
    Local Instance api : PipelineAPI
      := {
          spec :=
            {| Arg.named_args := [inbounds_multiplier_spec; outbounds_multiplier_spec; inbounds_spec; outbounds_spec; use_bitwidth_in_spec; use_bitwidth_out_spec]
               ; Arg.anon_args := [src_n_spec; sc_spec; src_limbwidth_spec; dst_limbwidth_spec]
               ; Arg.anon_opt_args := []
               ; Arg.anon_opt_repeated_arg := Some (function_to_synthesize_spec BaseConversion.valid_names) |};

          parse_args opts args
          := let '((inbounds_multiplier, outbounds_multiplier, inbounds, outbounds, use_bitwidth_in, use_bitwidth_out),
                   ((str_src_n, src_n), (str_sc, (s, c)), (str_src_limbwidth, src_limbwidth), (str_dst_limbwidth, dst_limbwidth)),
                   tt,
                   requests) := args in
             let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
             let to_bool ls := (0 <? List.length ls)%nat in
             let to_string_opt ls := choose_one_of_many (List.map (@snd _ _) ls) in
             let inbounds_multiplier := to_string_opt inbounds_multiplier in
             let outbounds_multiplier := to_string_opt outbounds_multiplier in
             let inbounds := to_string_opt inbounds in
             let outbounds := to_string_opt outbounds in
             let use_bitwidth_in := to_bool use_bitwidth_in in
             let use_bitwidth_out := to_bool use_bitwidth_out in
             let '(str_inbounds_multiplier, inbounds_multiplier) := parse_dirbounds_multiplier "in" (inl inbounds_multiplier) in
             let '(str_outbounds_multiplier, outbounds_multiplier) := parse_dirbounds_multiplier "out" (inl outbounds_multiplier) in
             let '(str_inbounds, inbounds) := parse_dirbounds "in" (inl inbounds) use_bitwidth_in in
             let '(str_outbounds, outbounds) := parse_dirbounds "out" (inl outbounds) use_bitwidth_out in
             match join_errors
                     (join_errors
                        inbounds_multiplier
                        outbounds_multiplier)
                     (join_errors
                        inbounds
                        outbounds)
             with
             | inr errs => inr errs
             | inl ((inbounds_multiplier, outbounds_multiplier), (inbounds, outbounds))
               => inl ((str_src_n, str_sc, str_src_limbwidth, str_dst_limbwidth, str_inbounds_multiplier, str_outbounds_multiplier, use_bitwidth_in, use_bitwidth_out, str_inbounds, str_outbounds, show_requests),
                       (src_n, s, c, src_limbwidth, dst_limbwidth, inbounds_multiplier, outbounds_multiplier, inbounds, outbounds, requests))
             end;

          show_lines_args :=
            fun '((str_src_n, str_sc, str_src_limbwidth, str_dst_limbwidth, str_inbounds_multiplier, str_outbounds_multiplier, use_bitwidth_in, use_bitwidth_out, str_inbounds, str_outbounds, show_requests),
                  (src_n, s, c, src_limbwidth, dst_limbwidth, inbounds_multiplier, outbounds_multiplier, inbounds, outbounds, requests))
            => ["requested operations: " ++ show_requests;
               "src_n = " ++ show src_n ++ " (from """ ++ str_src_n ++ """)";
               "s-c = " ++ PowersOfTwo.show_Z s ++ " - " ++ show_c c ++ " (from """ ++ str_sc ++ """)";
               "src_limbwidth = " ++ show src_limbwidth ++ " (from """ ++ str_src_limbwidth ++ """)";
               "dst_limbwidth = " ++ show dst_limbwidth ++ " (from """ ++ str_dst_limbwidth ++ """)";
               "inbounds_multiplier = " ++ show inbounds_multiplier ++ " (from """ ++ str_inbounds_multiplier ++ """)";
               "outbounds_multiplier = " ++ show outbounds_multiplier ++ " (from """ ++ str_outbounds_multiplier ++ """)";
               "inbounds = " ++ show inbounds ++ " (from """ ++ str_inbounds ++ """ and use_bithwidth_in = " ++ show use_bitwidth_in ++ ")";
               "outbounds = " ++ show outbounds ++ " (from """ ++ str_outbounds ++ """ and use_bithwidth_out = " ++ show use_bitwidth_out ++ ")"];

          Synthesize
          := fun _ opts '(src_n, s, c, src_limbwidth, dst_limbwidth, inbounds_multiplier, outbounds_multiplier, inbounds, outbounds, requests) comment_header prefix
             => BaseConversion.Synthesize s c src_n src_limbwidth dst_limbwidth machine_wordsize inbounds_multiplier outbounds_multiplier inbounds outbounds comment_header prefix requests
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               {io_driver : IODriverAPI A}
               (argv : list string)
      : A
      := Parameterized.PipelineMain argv.
  End BaseConversion.
End ForExtraction.
