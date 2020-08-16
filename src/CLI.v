Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.HexString.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.ParseArithmeticToTaps.
Require Import Crypto.Util.Strings.Parse.Common.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.Show.
Require Crypto.PushButtonSynthesis.SaturatedSolinas.
Require Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.PushButtonSynthesis.BaseConversion.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Stringification.C.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Stringification.Rust.
Require Import Crypto.Stringification.Go.
Require Import Crypto.Stringification.Java.
Require Import Crypto.Stringification.JSON.
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
             | None => inr ["Could not parse '" ++ s ++ "' as a Q for --" ++ dir ++ "bounds-multiplier"]%string
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
  Definition quote (s : string) : string
    := if List.existsb (fun ch => List.existsb (fun badch => badch =? ch)%char
                                               [" "; "("; ")"]%char)
                       (String.list_ascii_of_string s)
       then "'" ++ s ++ "'"
       else s.

  Definition CollectErrors
             {machine_wordsize : machine_wordsize_opt}
             {output_language_api : ToString.OutputLanguageAPI}
             (res : list (string * Pipeline.ErrorT (list string)) + list string)
    : list (list string) + list (list string)
    := match res with
       | inl res
         => let header := hd "" (List.map (@fst _ _) res) in
            let res :=
                List.fold_right
                  (fun '(name, res) rest
                   => match res, rest with
                      | ErrorT.Error err, rest
                        => let in_name := ("In " ++ name ++ ":") in
                           let cur :=
                               match show_lines false err with
                               | [serr] => [in_name ++ " " ++ serr]
                               | serr => in_name::serr
                               end in
                           let rest := match rest with inl _ => nil | inr rest => rest end in
                           inr (cur :: rest)
                      | ErrorT.Success v, inr ls => inr ls
                      | ErrorT.Success v, inl ls
                        => inl (v :: ls)
                      end)
                  (inl nil)
                  res in
            match res with
            | inl ls => inl ls
            | inr err => inr ([header]::err)
            end
       | inr res
         => inr [res]
       end.

  Class supported_languagesT := supported_languages : list (string * ToString.OutputLanguageAPI).

  (** N.B. The order matters, as the first element of the supported
      languages list is used as the default. *)
  Definition default_supported_languages : supported_languagesT
    := [("C", ToString.OutputCAPI)
        ; ("Rust", Rust.OutputRustAPI)
        ; ("Go", Go.OutputGoAPI)
        ; ("Java", Java.OutputJavaAPI)
        ; ("JSON", JSON.OutputJSONAPI)].

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
  Definition static_spec : named_argT
    := ([Arg.long_key "static"], Arg.Unit, ["Declare the functions as static, i.e., local to the file."]).
  Definition internal_static_spec : named_argT
    := ([Arg.long_key "internal-static"], Arg.Unit, ["Declare internal functions as static, i.e., local to the file."]).
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
  Definition cmovznz_by_mul_spec : named_argT
    := ([Arg.long_key "cmovznz-by-mul"], Arg.Unit, ["Use an alternative implementation of cmovznz using multiplication rather than bitwise-and with -1."]).
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
        ["The (improper) fraction by which the bounds of each input limb are scaled (default: " ++ show false default_inbounds_multiplier ++ ")"]).
  Definition default_outbounds_multiplier := 1.
  Definition outbounds_multiplier_spec : named_argT
    := ([Arg.long_key "outbounds-multiplier"],
        Arg.String,
        ["The (improper) fraction by which the bounds of each output limb are scaled (default: " ++ show false default_outbounds_multiplier ++ ")"]).
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

  Definition collapse_list_default {A} (default : A) (ls : list A)
    := List.hd default (List.rev ls).

  Definition join_errors {A B} (x : A + list string) (y : B + list string) : (A * B) + list string
    := match x, y with
       | inr errs1, inr errs2 => inr (errs1 ++ errs2)%list
       | inr err, inl _ | inl _, inr err => inr err
       | inl x, inl y => inl (x, y)
       end.

  (** We define a class for holding the various options we might pass to [Synthesize] *)
  Class SynthesizeOptions :=
    {
      (** Is the code static / inlined *)
      static :> static_opt
      (** Is the internal code static / inlined *)
      ; internal_static :> internal_static_opt
      (** Should we only use signed integers *)
      ; only_signed :> only_signed_opt
      (** Should we emit expressions requiring cmov *)
      ; no_select :> no_select_opt
      (** Should we emit primitive operations *)
      ; emit_primitives :> emit_primitives_opt
      (** Should we use the alternate implementation of cmovznz *)
      ; use_mul_for_cmovznz :> use_mul_for_cmovznz_opt
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
      (** What method should we use for rewriting? *)
      ; low_level_rewriter_method :> low_level_rewriter_method_opt
        := default_low_level_rewriter_method
      (** What's the bitwidth? *)
      ; machine_wordsize :> machine_wordsize_opt
    }.

  Definition common_optional_options {supported_languages : supported_languagesT}
    := [lang_spec
        ; static_spec
        ; internal_static_spec
        ; no_wide_int_spec
        ; widen_carry_spec
        ; widen_bytes_spec
        ; no_select_spec
        ; split_multiret_spec
        ; value_barrier_spec
        ; no_primitives_spec
        ; cmovznz_by_mul_spec
        ; only_signed_spec
       ].

  Definition parse_common_optional_options
             {supported_languages : supported_languagesT}
             {machine_wordsizev : machine_wordsize_opt}
             (data : Arg.keyed_spec_list_data common_optional_options)
    : (SynthesizeOptions * ToString.OutputLanguageAPI) + list string
    := let '(langv
             , staticv
             , internal_staticv
             , no_wide_intv
             , widen_carryv
             , widen_bytesv
             , no_selectv
             , split_multiretv
             , value_barrierv
             , no_primitivesv
             , cmovznz_by_mulv
             , only_signedv
            ) := data in
       let to_bool ls := (0 <? List.length ls)%nat in
       let res
           := ({| static := to_bool staticv
                  ; internal_static := to_bool internal_staticv
                  ; widen_carry := to_bool widen_carryv
                  ; widen_bytes := to_bool widen_bytesv
                  ; no_select := to_bool no_selectv
                  ; only_signed := to_bool only_signedv
                  ; should_split_mul := to_bool no_wide_intv
                  ; should_split_multiret := to_bool split_multiretv
                  ; unfold_value_barrier := negb (to_bool value_barrierv)
                  ; use_mul_for_cmovznz := to_bool cmovznz_by_mulv
                  ; emit_primitives := negb (to_bool no_primitivesv)
               |},
               snd (List.hd lang_default langv)) in
       match langv with
       | [] | [_] => inl res
       | opts => inr ["Only one language specification with --lang is allowed; multiple languages were requested: " ++ String.concat ", " (List.map (@fst _ _) opts)]
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
          list (string * Pipeline.ErrorT (list string))
    }.

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
        : list (string * Pipeline.ErrorT (list string)) + list string
        := let prefix := ("fiat_" ++ curve_description ++ "_")%string in
           let header :=
               ((["Autogenerated: " ++ invocation
                  ; "curve description: " ++ curve_description
                  ; "machine_wordsize = " ++ show false (machine_wordsize:Z) ++ " (from """ ++ str_machine_wordsize ++ """)"]%string)
                  ++ show_lines_args args)%list in
           inl (Synthesize (snd args) header prefix).

      Definition strip_trailing_spaces (s : string) : string
        := String.concat String.NewLine (List.map String.rtrim (String.split String.NewLine s)).

      Definition ProcessedLines
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (str_machine_wordsize : string)
                 (args : ArgsT)
        : list string + list string
        := match CollectErrors (PipelineLines invocation curve_description str_machine_wordsize args) with
           | inl ls
             => inl
                  (List.flat_map (fun s => ((List.map (fun s => s ++ String.NewLine) (List.map strip_trailing_spaces s))%string)
                                             ++ [String.NewLine])%list
                                 ls)
           | inr nil => inr nil
           | inr (l :: ls)
             => inr (l ++ (List.flat_map
                             (fun e => String.NewLine :: e)
                             ls))%list
           end.

      Definition Pipeline
                 {A}
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (str_machine_wordsize : string)
                 (args : ArgsT)
                 (success : list string -> A)
                 (error : list string -> A)
        : A
        := match ProcessedLines invocation curve_description str_machine_wordsize args with
           | inl s => success s
           | inr s => error s
           end.

      Definition PipelineMain
                 {supported_languages : supported_languagesT}
                 {A}
                 (argv : list string)
                 (success : list string -> A)
                 (error : list string -> A)
        : A
        := let invocation := String.concat " " (List.map quote argv) in
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
                | inl (opts, output_language_api)
                  => match parse_args (named_data, anon_data, anon_opt_data, anon_opt_repeated_data) with
                     | inl args
                       => Pipeline invocation curve_description str_machine_wordsize args success error
                     | inr errs => error errs
                     end
                | inr errs => error errs
                end
           | ErrorT.Error err => error (Arg.show_list_parse_error full_spec err)
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
             | None, NumLimbs n => inr ["Internal error: get_num_limbs (on (" ++ PowersOfTwo.show_Z false s ++ ", " ++ show_c false c ++ ", " ++ show false (machine_wordsize:Z) ++ ", " ++ show false n ++ ")) returned None even though the argument was NumLimbs"]
             | None, Auto idx => inr ["Invalid index " ++ show false idx ++ " when guessing the number of limbs for s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ "; valid indices must index into the list " ++ show false (get_possible_limbs s c machine_wordsize) ++ "."]
             | Some n, _
               => inl
                    ((str_n, str_sc, str_tight_bounds_multiplier, show_requests),
                     (n, s, c, tight_bounds_multiplier, requests))
             end;

          show_lines_args :=
            fun '((str_n, str_sc, str_tight_bounds_multiplier, show_requests),
                  (n, s, c, tight_bounds_multiplier, requests))
            => ["requested operations: " ++ show_requests;
               "n = " ++ show false n ++ " (from """ ++ str_n ++ """)";
               "s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """)";
               "tight_bounds_multiplier = " ++ show false (tight_bounds_multiplier:Q) ++ " (from """ ++ str_tight_bounds_multiplier ++ """)"]%string;

          Synthesize
          := fun _ opts '(n, s, c, tight_bounds_multiplier, requests) comment_header prefix
             => UnsaturatedSolinas.Synthesize n s c machine_wordsize comment_header prefix requests;
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               (argv : list string)
               (success : list string -> A)
               (error : list string -> A)
      : A
      := Parameterized.PipelineMain argv success error.
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
               "m = " ++ Hex.show_Z false m ++ " (from """ ++ str_m ++ """)";
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
               (argv : list string)
               (success : list string -> A)
               (error : list string -> A)
      : A
      := Parameterized.PipelineMain argv success error.
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
               "s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """)"];

          Synthesize
          := fun _ opts '(s, c, requests) comment_header prefix
             => SaturatedSolinas.Synthesize s c machine_wordsize comment_header prefix requests
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               (argv : list string)
               (success : list string -> A)
               (error : list string -> A)
      : A
      := Parameterized.PipelineMain argv success error.
  End SaturatedSolinas.

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
             let to_string_opt ls := List.nth_error (List.map (@snd _ _) ls) 0 in
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
               "src_n = " ++ show false src_n ++ " (from """ ++ str_src_n ++ """)";
               "s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """)";
               "src_limbwidth = " ++ show false src_limbwidth ++ " (from """ ++ str_src_limbwidth ++ """)";
               "dst_limbwidth = " ++ show false dst_limbwidth ++ " (from """ ++ str_dst_limbwidth ++ """)";
               "inbounds_multiplier = " ++ show false inbounds_multiplier ++ " (from """ ++ str_inbounds_multiplier ++ """)";
               "outbounds_multiplier = " ++ show false outbounds_multiplier ++ " (from """ ++ str_outbounds_multiplier ++ """)";
               "inbounds = " ++ show false inbounds ++ " (from """ ++ str_inbounds ++ """ and use_bithwidth_in = " ++ show false use_bitwidth_in ++ ")";
               "outbounds = " ++ show false outbounds ++ " (from """ ++ str_outbounds ++ """ and use_bithwidth_out = " ++ show false use_bitwidth_out ++ ")"];

          Synthesize
          := fun _ opts '(src_n, s, c, src_limbwidth, dst_limbwidth, inbounds_multiplier, outbounds_multiplier, inbounds, outbounds, requests) comment_header prefix
             => BaseConversion.Synthesize s c src_n src_limbwidth dst_limbwidth machine_wordsize inbounds_multiplier outbounds_multiplier inbounds outbounds comment_header prefix requests
        }.

    Definition PipelineMain
               {supported_languages : supported_languagesT}
               {A}
               (argv : list string)
               (success : list string -> A)
               (error : list string -> A)
      : A
      := Parameterized.PipelineMain argv success error.
  End BaseConversion.
End ForExtraction.
