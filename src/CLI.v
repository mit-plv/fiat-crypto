Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import Crypto.Util.Strings.ParseArithmetic.
Require Import Crypto.Util.Strings.ParseArithmeticToTaps.
Require Import Crypto.Util.Option.
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
Import ListNotations. Local Open Scope Z_scope. Local Open Scope string_scope.

Import
  Stringification.Language.Compilers
  Stringification.C.Compilers.

Module ForExtraction.
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
  Definition parse_inbounds_multiplier (s : string) : option (option Q)
    := option_map (@Some _) (parse_Q s).

  Definition show_c : Show (list (Z * Z))
    := @show_list _ (@show_prod _ _ PowersOfTwo.show_Z Decimal.show_Z).

  Local Open Scope string_scope.
  Local Notation NewLine := (String "010" "") (only parsing).

  (** TODO: Write a better quoter and maybe move this elsewhere *)
  Definition quote (s : string) : string
    := if List.existsb (Ascii.eqb " ") (String.to_list s)
       then "'" ++ s ++ "'"
       else s.

  Definition CollectErrors
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

  Definition supported_languages : list (string * ToString.OutputLanguageAPI)
    := [("C", ToString.OutputCAPI)
       ; ("Rust", Rust.OutputRustAPI)].

  Definition curve_description_help
    := "  curve_description       A string which will be prefixed to every function name generated".
  Definition lang_help
    := "  LANGUAGE                The output language code should be emitted in.  Defaults to C if no language is given.  Case-sensitive."
         ++ String.NewLine ++
       "                            Valid options are: " ++ String.concat ", " (List.map (@fst _ _) supported_languages).
  Definition total_help_indent
    := "                          ".
  Definition static_and_help
    := ("--static", "Declare the functions as static, i.e., local to the file.").
  Definition no_wide_int_and_help
    := ("--no-wide-int", "Don't use integers wider than the bitwidth.").
  Definition widen_carry_and_help
    := ("--widen-carry", "Widen carry bit integer types to either the byte type, or to the full bitwidth if --widen-bytes is also passed.").
  Definition widen_bytes_and_help
    := ("--widen-bytes", "Widen byte types to the full bitwidth.").
  Definition no_primitives_and_help
    := ("--no-primitives", "Suppress the generation of the bodies of primitive operations such as addcarryx, subborrowx, cmovznz, mulx, etc.").
  Definition cmovznz_by_mul_and_help
    := ("--cmovznz-by-mul", "Use an alternative implementation of cmovznz using multiplication rather than bitwise-and with -1.").
  Definition n_help
    := "  n                       The number of limbs, or the literal '(auto)' or '(autoN)' for a non-negative number N, to automatically guess the number of limbs".
  Definition sc_help
    := "  s-c                     The prime, which must be expressed as a difference of a power of two and a small field element (e.g., '2^255 - 19', '2^448 - 2^224 - 1')".
  Definition m_help
    := "  m                       The prime (e.g., '2^434 - (2^216*3^137 - 1)')".
  Definition machine_wordsize_help
    := "  machine_wordsize        The machine bitwidth (e.g., 32 or 64)".
  Definition src_n_help
    := "  src_n                   The number of limbs in the input".
  Definition src_limbwidth_help
    := "  src_limbwidth           The limbwidth of the input field element".
  Definition dst_limbwidth_help
    := "  dst_limbwidth           The limbwidth of the field element to be returned".
  Definition max_help
    := "  max                     The upperbound (strict / exclusive) on the input field element".
  Definition inbounds_multiplier_help
    := "  inbounds_multiplier     The (improper) fraction by which the bounds of each limb are scaled".

  Definition function_to_synthesize_help (valid_names : string)
    := "  function_to_synthesize  A space-separated list of functions that should be synthesized.  If no functions are given, all functions are synthesized."
         ++ String.NewLine ++
         "                            Valid options are " ++ valid_names.

  Definition common_optional_options
    := [static_and_help
        ; no_wide_int_and_help
        ; widen_carry_and_help
        ; widen_bytes_and_help
        ; no_primitives_and_help
        ; cmovznz_by_mul_and_help
       ].
  Definition common_usage_opts
    := String.concat " " (List.map (fun '(opt, _) => "[" ++ opt ++ "]") common_optional_options).

  Definition to_help (s : string * string)
    := let opt := "  " ++ fst s in
       let descr := snd s in
       opt ++ String.substring 0 (String.length total_help_indent - String.length opt) total_help_indent ++ descr.


  Record > Dyn := dyn { dyn_ty : Type ; dyn_val :> option dyn_ty }.
  Arguments dyn {_} _.

  Fixpoint parse_resultL' (acc : Type) (ls : list (string (* name *) * string (* string value *) * Dyn))
    : Type
    := match ls with
       | nil => acc
       | cons (_, _, {| dyn_ty := T |}) ls'
         => parse_resultL' (acc * T) ls'
       end.
  Definition parse_resultL (ls : list (string (* name *) * string (* string value *) * Dyn))
    := match ls return Type with
       | nil => unit
       | cons (_, _, {| dyn_ty := T |}) ls'
         => parse_resultL' T ls' + list string
       end%type.

  Fixpoint parse_many' {accT : Type} (acc : accT)
           (ls : list (string (* name *) * string (* string value *) * Dyn))
    : parse_resultL' accT ls + list string
    := match ls return parse_resultL' accT ls + list string with
       | nil => inl acc
       | cons (_, _, {| dyn_val := Some v |}) ls'
         => @parse_many' _ (acc, v) ls'
       | cons (name, str_val, {| dyn_val := None |}) ls'
         => let err_ls := match @parse_many' _ tt ls' with
                          | inl _ => nil
                          | inr err_ls => err_ls
                          end in
            inr ((name ++ " (" ++ str_val ++ ")")%string :: err_ls)
       end.

  Definition parse_many
             (ls : list (string (* name *) * string (* string value *) * Dyn))
    : parse_resultL ls
    := let transform_err T (v : T + list string)
           := match v with
              | inl v => inl v
              | inr nil => inr ["Internal Error: Parse failure without an error message"]
              | inr ls => inr ["Could not parse " ++ String.concat " nor " ls]
              end%string in
       match ls with
       | nil => tt
       | cons (_, _, {| dyn_val := Some v |}) ls'
         => transform_err _ (@parse_many' _ v ls')
       | cons (name, str_val, {| dyn_val := None |}) ls'
         => let err_ls := match @parse_many' _ tt ls' with
                          | inl _ => nil
                          | inr err_ls => err_ls
                          end in
            transform_err _ (inr ((name ++ " (" ++ str_val ++ ")")%string :: err_ls))
       end.

  (** We define a class for holding the various options we might pass to [Synthesize] *)
  Class SynthesizeOptions :=
    {
      (** Is the code static / inlined *)
      static :> static_opt

      (** Should we emit primitive operations *)
      ; emit_primitives :> emit_primitives_opt
      (** Should we use the alternate implementation of cmovznz *)
      ; use_mul_for_cmovznz :> use_mul_for_cmovznz_opt
      (** Should we split apart oversized operations? *)
      ; should_split_mul :> should_split_mul_opt
      (** Should we widen the carry to the full bitwidth? *)
      ; widen_carry :> widen_carry_opt
      (** Should we widen the byte type to the full bitwidth? *)
      ; widen_bytes :> widen_bytes_opt
    }.

  (** We define a class for the various operations that are specific to a pipeline *)
  Class PipelineAPI :=
    {
      (** Type of arguments parsed from the command line *)
      ParsedArgsT : Type;
      (** Type of (unparsed) arguments remembered from the command line *)
      StringArgsT : Type;
      ArgsT := (StringArgsT * ParsedArgsT)%type;

      (** Takes in argv except without the binary name and without any
          general options (such as language), and parses the
          curve-specific arguments, returning either [Some (inl
          value)], [Some (inr errors)], or [None] if there are not
          enough arguments and the usage string should be displayed. *)
      parse_args : list string -> option (ArgsT + list string);

      (** Renders a header at the top displaying the command line
          arguments.  Will be wrapped in a comment block *)
      show_lines_args : ArgsT -> list string;

      (** The part of the usage-string for arguments after curve_description *)
      pipeline_usage_string : string;
      (** The list of help strings (to be joined by newlines) *)
      help_lines : list string;

      (** The Synthesize function from the pipeline *)
      (** N.B. [comment_header] will be passed in *without* wrapping
          it in a comment block first *)
      Synthesize : forall
          {output_language_api : ToString.OutputLanguageAPI}
          {synthesize_opts : SynthesizeOptions}
          (args : ParsedArgsT) (comment_header : list string) (function_name_prefix : string),
          list (string * Pipeline.ErrorT (list string))
    }.

  Module Parameterized.
    Section __.
      Context {api : PipelineAPI}.

      Definition PipelineLines
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (args : ArgsT)
        : list (string * Pipeline.ErrorT (list string)) + list string
        := let prefix := ("fiat_" ++ curve_description ++ "_")%string in
           let header :=
               ((["Autogenerated: " ++ invocation;
                    "curve description: " ++ curve_description]%string)
                  ++ show_lines_args args)%list in
           inl (Synthesize (snd args) header prefix).

      Definition ProcessedLines
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (args : ArgsT)
        : list string + list string
        := match CollectErrors (PipelineLines invocation curve_description args) with
           | inl ls
             => inl
                  (List.map (fun s => String.concat NewLine s ++ NewLine ++ NewLine)
                            ls)
           | inr nil => inr nil
           | inr (l :: ls)
             => inr (l ++ (List.flat_map
                             (fun e => NewLine :: e)
                             ls))%list
           end.

      Definition Pipeline
                 {A}
                 {output_language_api : ToString.OutputLanguageAPI}
                 {synthesize_opts : SynthesizeOptions}
                 (invocation : string)
                 (curve_description : string)
                 (args : ArgsT)
                 (success : list string -> A)
                 (error : list string -> A)
        : A
        := match ProcessedLines invocation curve_description args with
           | inl s => success s
           | inr s => error s
           end.

      (** if [opt] is in [tl argv], remove all instances of it, and
          return [(filter-out opt argv, true)]; otherwise, return
          [(argv, false)] *)
      Definition argv_to_contains_opt_and_argv (opt : string) (argv : list string)
        : list string * bool
        := match argv with
           | prog_name :: rest
             => let is_opt arg := (arg =? opt)%string in
                (prog_name :: filter (fun arg => negb (is_opt arg)) rest,
                 existsb is_opt rest)
           | _ => (argv, false)
           end.

      (** return the remainder of all elements of [argv] starting with
          [opt], and all elements which do not start with [opt] *)
      Definition argv_to_startswith_opt_and_argv (opt : string) (argv : list string)
        := let '(opts, argv) := List.partition (String.contains 0 opt) argv in
           (argv,
            List.map (fun s => String.substring (String.length opt) (String.length s) s) opts).

      Definition argv_to_language_and_argv (argv : list string)
        : list string * (ToString.OutputLanguageAPI + list string)
        := let '(argv, opts) := argv_to_startswith_opt_and_argv "--lang=" argv in
           (argv,
            match opts with
            | [] => inl (* if no is --lang=<something known>, default to C *)
                      ToString.OutputCAPI
            | [lang]
              => match List.filter (fun '(known_lang, _) => String.eqb lang known_lang) supported_languages with
                 | [] => inr ["Unknown language " ++ lang ++ " requested; supported languages are " ++ String.concat ", " (List.map (@fst _ _) supported_languages)]
                 | [(_, output_api)] => inl output_api
                 | _ => inr ["Internal Error: Multiple languages exist with the same name (" ++ lang ++ ")"]
                 end
            | _
              => inr ["Only one language specification with --lang is allowed; multiple languages were requested: " ++ String.concat ", " opts]
            end).

      Definition PipelineMain
                 {A}
                 (argv : list string)
                 (success : list string -> A)
                 (error : list string -> A)
        : A
        := let invocation := String.concat " " (List.map quote argv) in
           let on_wrong_argv _ :=
               match argv with
               | nil => error ["empty argv"]
               | prog::args
                 => error ((["USAGE: " ++ prog ++ " [--lang=LANGUAGE] " ++ common_usage_opts ++ " curve_description " ++ pipeline_usage_string;
                               "Got " ++ show false (List.length args) ++ " arguments.";
                               "";
                               lang_help]%string)
                             ++ List.map to_help common_optional_options
                             ++ [curve_description_help]
                             ++ help_lines
                             ++ [""])%list
               end in
           let '(argv, output_language_api) := argv_to_language_and_argv argv in
           let '(argv, staticv) := argv_to_contains_opt_and_argv "--static" argv in
           let '(argv, no_wide_intsv) := argv_to_contains_opt_and_argv "--no-wide-int" argv in
           let '(argv, use_mul_for_cmovznzv) := argv_to_contains_opt_and_argv "--cmovznz-by-mul" argv in
           let '(argv, widen_carryv) := argv_to_contains_opt_and_argv "--widen-carry" argv in
           let '(argv, widen_bytesv) := argv_to_contains_opt_and_argv "--widen-bytes" argv in
           let '(argv, no_primitivesv) := argv_to_contains_opt_and_argv "--no-primitives" argv in
           match output_language_api, argv with
           | inl output_language_api, _::curve_description::args
             => match parse_args args with
                | Some (inl args)
                  => let opts
                         := {| static := staticv
                               ; use_mul_for_cmovznz := use_mul_for_cmovznzv
                               ; widen_carry := widen_carryv
                               ; widen_bytes := widen_bytesv
                               ; should_split_mul := no_wide_intsv
                               ; emit_primitives := negb no_primitivesv |} in
                     Pipeline invocation curve_description args success error
                | Some (inr errs)
                  => error errs
                | None => on_wrong_argv tt
                end
           | inr errs, _ => error errs
           | _, _ => on_wrong_argv tt
           end.
    End __.
  End Parameterized.

  Module UnsaturatedSolinas.
    Local Instance api : PipelineAPI
      := {
          parse_args (args : list string)
          := match args with
             | n::sc::machine_wordsize::requests
               => let str_n := n in
                  let str_machine_wordsize := machine_wordsize in
                  let str_sc := sc in
                  let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
                  Some
                    match parse_many [("n", n, parse_n n:Dyn)
                                      ; ("machine_wordsize", machine_wordsize, parse_machine_wordsize machine_wordsize:Dyn)
                                      ; ("s-c", sc, parse_sc sc:Dyn)] with
                    | inr errs => inr errs
                    | inl (n, machine_wordsize, (s, c))
                      => match get_num_limbs s c machine_wordsize n, n with
                         | None, NumLimbs n => inr ["Internal error: get_num_limbs (on (" ++ PowersOfTwo.show_Z false s ++ ", " ++ show_c false c ++ ", " ++ show false machine_wordsize ++ ", " ++ show false n ++ ")) returned None even though the argument was NumLimbs"]
                         | None, Auto idx => inr ["Invalid index " ++ show false idx ++ " when guessing the number of limbs for s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ "; valid indices must index into the list " ++ show false (get_possible_limbs s c machine_wordsize) ++ "."]
                         | Some n, _
                           => inl
                                ((str_n, str_machine_wordsize, str_sc, show_requests),
                                 (n, machine_wordsize, s, c, requests))
                         end
                    end
             | _ => None
             end;

          show_lines_args :=
            fun '((str_n, str_machine_wordsize, str_sc, show_requests),
                  (n, machine_wordsize, s, c, requests))
            => ["requested operations: " ++ show_requests;
                  "n = " ++ show false n ++ " (from """ ++ str_n ++ """)";
                  "s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """)";
                  "machine_wordsize = " ++ show false machine_wordsize ++ " (from """ ++ str_machine_wordsize ++ """)"]%string;

          pipeline_usage_string := "n s-c machine_wordsize [function_to_synthesize*]";

          help_lines := [n_help;
                           sc_help;
                           machine_wordsize_help;
                           function_to_synthesize_help UnsaturatedSolinas.valid_names];

          Synthesize
          := fun _ opts '(n, machine_wordsize, s, c, requests) comment_header prefix
             => UnsaturatedSolinas.Synthesize n s c machine_wordsize comment_header prefix requests
        }.

    Definition PipelineMain
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
          parse_args (args : list string)
          := match args with
             | m::machine_wordsize::requests
               => let str_machine_wordsize := machine_wordsize in
                  let str_m := m in
                  let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
                  Some
                    match parse_many [("machine_wordsize", machine_wordsize, parse_machine_wordsize machine_wordsize:Dyn);
                                        ("m", m, parse_m m:Dyn)] with
                    | inr errs => inr errs
                    | inl (machine_wordsize, m)
                      => inl ((str_machine_wordsize, str_m, show_requests),
                              (machine_wordsize, m, requests))
                    end
             | _ => None
             end;

          show_lines_args :=
            fun '((str_machine_wordsize, str_m, show_requests),
                  (machine_wordsize, m, requests))
            => ["requested operations: " ++ show_requests;
                  "m = " ++ Hex.show_Z false m ++ " (from """ ++ str_m ++ """)";
                  "machine_wordsize = " ++ show false machine_wordsize ++ " (from """ ++ str_machine_wordsize ++ """)";
                  "                                                                  ";
                  "NOTE: In addition to the bounds specified above each function, all";
                  "  functions synthesized for this Montgomery arithmetic require the";
                  "  input to be strictly less than the prime modulus (m), and also  ";
                  "  require the input to be in the unique saturated representation. ";
                  "  All functions also ensure that these two properties are true of ";
                  "  return values.                                                  "];

          pipeline_usage_string := "m machine_wordsize [function_to_synthesize*]";

          help_lines := [m_help;
                           machine_wordsize_help;
                           function_to_synthesize_help WordByWordMontgomery.valid_names];

          Synthesize
          := fun _ opts '(machine_wordsize, m, requests) comment_header prefix
             => WordByWordMontgomery.Synthesize m machine_wordsize comment_header prefix requests
        }.

    Definition PipelineMain
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
          parse_args (args : list string)
          := match args with
             | sc::machine_wordsize::requests
               => let str_machine_wordsize := machine_wordsize in
                  let str_sc := sc in
                  let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
                  Some
                    match parse_many [("machine_wordsize", machine_wordsize, parse_machine_wordsize machine_wordsize:Dyn)
                                      ; ("s-c", sc, parse_sc sc:Dyn)] with
                    | inr errs => inr errs
                    | inl (machine_wordsize, (s, c))
                      => inl ((str_machine_wordsize, str_sc, show_requests),
                              (machine_wordsize, s, c, requests))
                    end
             | _ => None
             end;

          show_lines_args :=
            fun '((str_machine_wordsize, str_sc, show_requests),
                  (machine_wordsize, s, c, requests))
            => ["requested operations: " ++ show_requests;
                  "s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """)";
                  "machine_wordsize = " ++ show false machine_wordsize ++ " (from """ ++ str_machine_wordsize ++ """)"];

          pipeline_usage_string := "s-c machine_wordsize [function_to_synthesize*]";

          help_lines := [sc_help;
                           machine_wordsize_help;
                           function_to_synthesize_help SaturatedSolinas.valid_names];

          Synthesize
          := fun _ opts '(machine_wordsize, s, c, requests) comment_header prefix
             => SaturatedSolinas.Synthesize s c machine_wordsize comment_header prefix requests
        }.

    Definition PipelineMain
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
          parse_args (args : list string)
          := match args with
             | src_n::src_limbwidth::dst_limbwidth::machine_wordsize::max::inbounds_multiplier::requests
               => let str_src_n := src_n in
                  let str_src_limbwidth := src_limbwidth in
                  let str_dst_limbwidth := dst_limbwidth in
                  let str_machine_wordsize := machine_wordsize in
                  let str_max := max in
                  let str_inbounds_multiplier := inbounds_multiplier in
                  let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
                  Some
                    match parse_many [("src_n", src_n, parse_src_n src_n:Dyn)
                                      ; ("src_limbwidth", src_limbwidth, parse_limbwidth src_limbwidth:Dyn)
                                      ; ("dst_limbwidth", dst_limbwidth, parse_limbwidth dst_limbwidth:Dyn)
                                      ; ("machine_wordsize", machine_wordsize, parse_machine_wordsize machine_wordsize:Dyn)
                                      ; ("max", max, parse_max max:Dyn)
                                      ; ("inbounds_multiplier", inbounds_multiplier, parse_inbounds_multiplier inbounds_multiplier:Dyn)] with
                    | inr errs => inr errs
                    | inl (src_n, src_limbwidth, dst_limbwidth, machine_wordsize, max, inbounds_multiplier)
                      => inl ((str_src_n, str_src_limbwidth, str_dst_limbwidth, str_machine_wordsize, str_max, str_inbounds_multiplier, show_requests),
                              (src_n, src_limbwidth, dst_limbwidth, machine_wordsize, max, inbounds_multiplier, requests))
                    end
             | _ => None
             end;

          show_lines_args :=
            fun '((str_src_n, str_src_limbwidth, str_dst_limbwidth, str_machine_wordsize, str_max, str_inbounds_multiplier, show_requests),
                  (src_n, src_limbwidth, dst_limbwidth, machine_wordsize, max, inbounds_multiplier, requests))
            => ["requested operations: " ++ show_requests;
                  "src_n = " ++ show false src_n ++ " (from """ ++ str_src_n ++ """)";
                  "src_limbwidth = " ++ show false src_limbwidth ++ " (from """ ++ str_src_limbwidth ++ """)";
                  "dst_limbwidth = " ++ show false dst_limbwidth ++ " (from """ ++ str_dst_limbwidth ++ """)";
                  "machine_wordsize = " ++ show false machine_wordsize ++ " (from """ ++ str_machine_wordsize ++ """)";
                  "max = " ++ @show_option _ PowersOfTwo.show_Z false max ++ " (from """ ++ str_max ++ """)";
                  "inbounds_multiplier = " ++ show false inbounds_multiplier ++ " (from """ ++ str_inbounds_multiplier ++ """)"];

          pipeline_usage_string := "src_n src_limbwidth dst_limbwidth machine_wordsize max inbounds_multiplier [function_to_synthesize*]";

          help_lines := [src_n_help;
                           src_limbwidth_help;
                           dst_limbwidth_help;
                           machine_wordsize_help;
                           max_help;
                           inbounds_multiplier_help;
                           function_to_synthesize_help BaseConversion.valid_names];

          Synthesize
          := fun _ opts '(src_n, src_limbwidth, dst_limbwidth, machine_wordsize, max, inbounds_multiplier, requests) comment_header prefix
             => BaseConversion.Synthesize src_n src_limbwidth dst_limbwidth machine_wordsize max inbounds_multiplier comment_header prefix requests
        }.

    Definition PipelineMain
               {A}
               (argv : list string)
               (success : list string -> A)
               (error : list string -> A)
      : A
      := Parameterized.PipelineMain argv success error.
  End BaseConversion.
End ForExtraction.
