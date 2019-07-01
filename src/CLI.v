From Coq Require Import QArith.QArith ZArith.ZArith
     Strings.Ascii Lists.List Strings.String.
From Crypto.Util.Strings
     Require Import Decimal HexString ParseArithmetic
     ParseArithmeticToTaps Show.
From Crypto Require Import Util.Option Util.ErrorT
     UnsaturatedSolinasHeuristics CStringification BoundsPipeline.
From Crypto.PushButtonSynthesis Require SaturatedSolinas
     UnsaturatedSolinas WordByWordMontgomery.

Import ListNotations.
Import CStringification.Compilers.

Local Open Scope Z_scope. Local Open Scope string_scope.

Set Implicit Arguments.

Module ForExtraction.

  (* Workaround for lack of notation in 8.8 *)
  Local Notation "x =? y" := (if string_dec x y then true else false) : string_scope.

  (* Zoe: Towards a more extensible and modular CLI interface and less code duplication  *)

  (* CLI option as a parsed value and as a string *)
  Record CLI_option A :=
    MkOption { val: A; as_str: string; }.

  Inductive Mode :=
  | UnsaturatedSolinas
  | SaturatedSolinas
  | WordByWordMontgomery.

  (* Each mode has its own record type holding CL args specific to it *)
  Record UnsaturatedSolinasOpts :=
    MkUS { n : CLI_option MaybeLimbCount; sc_us : CLI_option (Z * list (Z * Z)) }.

  Record SaturatedSolinasOpts :=
    MkSS { sc_ss : CLI_option (Z * list (Z * Z)) }.

  Record WordByWordMontgomeryOpts :=
    MkWbW { m : CLI_option Z }.

  (* Zoe: We can avoid the dependent type here (that currently requires
     extraction hackery to work), by using a secong inductive type for
     modes and have mode options as constructor arguments. *)

  Definition Mode_options (m : Mode) : Type :=
    match m with
    | UnsaturatedSolinas => UnsaturatedSolinasOpts
    | SaturatedSolinas => SaturatedSolinasOpts
    | WordByWordMontgomery => WordByWordMontgomeryOpts
    end.

  (* Record for the current CLI options, indexed my the synthesis mode *)
  Record CLI_options (m : Mode) :=
    MkOptions {
        curve_description : string;
        mode_options : Mode_options m;
        machine_wordsize : CLI_option Z;
        requests : list string
      }.

  Definition CLIError := ErrorT (list string).

  (* Argument-parsing functions *)

  Definition parse_neg (s : string) : string * Z
    := match s with
       | String a b
         => if Ascii.ascii_dec a "-"
            then (b, -1)
            else if Ascii.ascii_dec a "+"
                 then (b, 1)
                 else (s, 1)
       | _ => (s, 1)
       end.
  Definition parse_Z (s : string) : option Z
    := z <- ParseArithmetic.parse_Z s;
         match snd z with
         | EmptyString => Some (fst z)
         | _ => None
         end.
  Definition parse_N (s : string) : option N
    := match parse_Z s with
       | Some Z0 => Some N0
       | Some (Zpos p) => Some (Npos p)
       | _ => None
       end.
  Definition parse_nat (s : string) : option nat
    := option_map N.to_nat (parse_N s).
  Definition parse_Q (s : string) : option Q
    := match List.map parse_Z (String.split "/" s) with
       | [Some num;Some (Zpos den)] => Some (Qmake num den)
       | [Some num] => Some (Qmake num 1)
       | _ => None
       end.
  Definition parse_bool (s : string) : option bool
    := if string_dec s "true"
       then Some true
       else if string_dec s "false"
            then Some false
            else None.


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
    := parseZ_arith s.

  Definition show_c : Show (list (Z * Z))
    := @show_list _ (@show_prod _ _ PowersOfTwo.show_Z Decimal.show_Z).

  Definition parse_CLI_option {A} (parse : string -> option A) (value : string) (name : string) : CLIError (CLI_option A) :=
    match parse value with
    | Some v => Success (MkOption v value)
    | None => Error ["Error: Could not parse " ++ name ++ " " ++ value ++ "." %string]
    end.


  (* Help printing *)
  Definition curve_description_help
    := "  curve_description       A string which will be prefixed to every function name generated".
  Definition n_help
    := "  n                       The number of limbs, or the literal '(auto)' or '(autoN)' for a non-negative number N, to automatically guess the number of limbs".
  Definition sc_help
    := "  s-c                     The prime, which must be expressed as a difference of a power of two and a small field element (e.g., '2^255 - 19', '2^448 - 2^224 - 1')".
  Definition m_help
    := "  m                       The prime (e.g., '2^434 - (2^216*3^137 - 1)')".
  Definition machine_wordsize_help
    := "  machine_wordsize        The machine bitwidth (e.g., 32 or 64)".
  Definition function_to_synthesize_help (valid_names : string)
    := "  function_to_synthesize  A space-separated list of functions that should be synthesized.  If no functions are given, all functions are synthesized."
         ++ String.NewLine ++
       "                            Valid options are " ++ valid_names.

  (* Usage information *)
  Definition print_help (m : Mode) (prog : string) (args : list string) :=
    let mode_args :=
        match m with
        | UnsaturatedSolinas => [n_help; sc_help]
        | SaturatedSolinas => [sc_help]
        | WordByWordMontgomery => [m_help]
        end in
    let mode_usage :=
        match m with
        | UnsaturatedSolinas => " curve_description n sc machine_wordsize [function_to_synthesize*]"
        | SaturatedSolinas => " curve_description sc machine_wordsize [function_to_synthesize*]"
        | WordByWordMontgomery => " curve_description m machine_wordsize [function_to_synthesize*]"
        end in
    let options_help :=
        ([""; curve_description_help] ++ [mode_usage] ++
         [machine_wordsize_help; function_to_synthesize_help (WordByWordMontgomery.valid_names); ""])%list in
    (["USAGE: " ++ prog ++ mode_usage;
      "Got " ++ show false (List.length args) ++ " arguments"]%string ++ options_help)%list.


  Open Scope error_scope.

  (* Parses command line options and constructs a CLI_options record *)
  Definition parse_CLI_options (mode : Mode) (argv : list string) : CLIError (CLI_options mode) :=
    match mode with
    | UnsaturatedSolinas =>
      match argv with
      | [] => Error ["Error: Arguments cannot be empty"]
      | _ :: backend :: curve_description :: n :: sc :: machine_wordsize :: requests =>
        n_opt <- parse_CLI_option parse_n n "n";
        sc_opt <- parse_CLI_option parse_sc sc "sc";
        mw_opt <- parse_CLI_option parse_machine_wordsize machine_wordsize "machine_wordsize";
        let mode_opt := MkUS n_opt sc_opt in
        Success (MkOptions UnsaturatedSolinas curve_description mode_opt mw_opt requests)
      | prog :: args => Error ("Error: Unrecognized arguments" :: print_help mode prog args)
      end
    | SaturatedSolinas =>
      match argv with
      | [] => Error ["Error: Arguments cannot be empty"]
      | _ :: backend :: curve_description :: sc :: machine_wordsize :: requests =>
        sc_opt <- parse_CLI_option parse_sc sc "sc";
        mw_opt <- parse_CLI_option parse_machine_wordsize machine_wordsize "machine_wordsize";
        let mode_opt := MkSS sc_opt in
        Success (MkOptions SaturatedSolinas curve_description mode_opt mw_opt requests)
      | prog :: args => Error ("Error: Unrecognized arguments" :: print_help mode prog args)
      end
    | WordByWordMontgomery =>
      match argv with
      | [] => Error ["Error: Arguments cannot be empty"]
      | _ :: backend :: curve_description :: m :: sc :: machine_wordsize :: requests =>
        m_opt <- parse_CLI_option parse_m m "m";
        sc_opt <- parse_CLI_option parse_sc sc "sc";
        mw_opt <- parse_CLI_option parse_machine_wordsize machine_wordsize "machine_wordsize";
        let mode_opt := MkWbW m_opt in
        Success (MkOptions WordByWordMontgomery curve_description mode_opt mw_opt requests)
      | prog :: args => Error ("Error: Unrecognized arguments" :: print_help mode prog args)
      end
    end.

  Local Open Scope string_scope.
  Local Notation NewLine := (String "010" "") (only parsing).

  (* Proccesses synthesis results and errors *)
  (* Zoe : Arguably processing this result type should not happen in this file *)
  Definition collect_results (res : list (string * Pipeline.ErrorT (list string)))
    : (CLIError (list string)) :=
    let header := hd "" (List.map (@fst _ _) res) in
    let res : list string + list string :=
        List.fold_right
          (fun '(name, res) rest =>
             match res, rest with
             | ErrorT.Error err, rest =>
               let in_name := ("In " ++ name ++ ":")%string in
               let cur :=
                   match show_lines false err with
                   | [serr] => [in_name ++ " " ++ serr]%string
                   | serr => in_name::serr
                   end in
               let rest := match rest with inl _ => nil | inr rest => rest end in
               inr (NewLine :: cur ++ rest)
             | ErrorT.Success v, inr ls => inr ls
             | ErrorT.Success s, inl ls =>
               let p := (String.concat NewLine s ++ NewLine ++ NewLine)%string in
               inl (p :: ls)
             end)%list (inl nil) res in
    match res with
    | inl ls => Success ls
    | inr err => Error (header::err)
    end.

  Definition get_limb_count (s : Z) (c : list (Z * Z)) (machine_wordsize: Z) (n : MaybeLimbCount)
    : CLIError nat :=
    match get_num_limbs s c machine_wordsize n, n with
    | None, NumLimbs n =>
      Error ["Internal error: get_num_limbs (on (" ++ PowersOfTwo.show_Z false s ++ ", " ++
             show_c false c ++ ", " ++ show false machine_wordsize ++ ", " ++ show false n ++
             ")) returned None even though the argument was NumLimbs"]
    | None, Auto idx =>
      Error ["Invalid index " ++ show false idx ++ " when guessing the number of limbs for s-c = " ++
             PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ "; valid indices must index into the list "
             ++ show false (get_possible_limbs s c machine_wordsize) ++ "."]
    | Some n, _ => Success n
    end.

  (* Constructs the header of the generated file *)
  (* Zoe : Arguably constructing the header of the file should not happen here *)
  Definition header (mode : Mode) (options : CLI_options mode) (prefix : string)
             (extra_comment : list string) (types_used : MSetPositive.PositiveSet.t)
    : CLIError (list string) :=
    let requests := requests options in
    let show_requests := match requests with nil => "(all)" | _ => String.concat ", " requests end in
    let (machine_wordsize, str_machine_wordsize) := machine_wordsize options in
    let suffix :=
        let mk_header := ToString.C.String.typedef_header in
        (extra_comment ++ mk_header prefix types_used ++ [""])%list in
    let mode_options_err :=
        match mode return CLI_options mode -> CLIError (list string) with
        | UnsaturatedSolinas =>
          fun options =>
            let (n, str_n) := n (mode_options options) in
            let 'MkOption (s, c) str_sc := sc_us (mode_options options) in
            limb_cnt <- get_limb_count s c machine_wordsize n;
            Success ["/* n = " ++ show false limb_cnt ++ " (from """ ++ str_n ++ """) */";
                     "/* s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """) */"]
        | SaturatedSolinas =>
          fun options =>
            let 'MkOption (s, c) str_sc := sc_ss (mode_options options) in
            Success ["/* s-c = " ++ PowersOfTwo.show_Z false s ++ " - " ++ show_c false c ++ " (from """ ++ str_sc ++ """) */"]
        | WordByWordMontgomery =>
          fun options =>
            let (m, str_m) := m (mode_options options) in
            Success ["/* m = " ++ Hex.show_Z false m ++ " (from """ ++ str_m ++ """) */"]
        end options in
    let extra_comment :=
        match mode with
        | UnsaturatedSolinas => []
        | SaturatedSolinas => []
        | WordByWordMontgomery =>
          ["/*                                                                    */";
           "/* NOTE: In addition to the bounds specified above each function, all */";
           "/*   functions synthesized for this Montgomery arithmetic require the */";
           "/*   input to be strictly less than the prime modulus (m), and also   */";
           "/*   require the input to be in the unique saturated representation.  */";
           "/*   All functions also ensure that these two properties are true of  */";
           "/*   return values.                                                   */"]%string
        end in
    mode_options <- mode_options_err;
    (* Zoe : TODO don't hardcode commenting style *)
    Success ("/* Autogenerated */" ::
             ("/* curve description: " ++ curve_description options ++ " */") ::
             ("/* requested operations: " ++ show_requests ++ " */") ::
             (mode_options ++
               ["/* machine_wordsize = " ++ show false machine_wordsize ++ " (from """ ++ str_machine_wordsize ++ """) */"]%string ++
               extra_comment ++ [""] ++ suffix)%list).

  (* Top-level synthesis dispatching *)
  Definition synthesize (mode : Mode) (options : CLI_options mode)
    : CLIError (list (string * Pipeline.ErrorT (list string))) :=
    let prefix := ("fiat_" ++ curve_description options ++ "_")%string in
    let requests := requests options in
    let (machine_wordsize, str_machine_wordsize) := machine_wordsize options in
    match mode return CLI_options mode -> _ with
    | UnsaturatedSolinas =>
      fun options =>
        let (n, str_n) := n (mode_options options) in
        let 'MkOption (s, c) str_sc := sc_us (mode_options options) in
        limb_cnt <- get_limb_count s c machine_wordsize n;
        let '(extra_header_comment, res, types_used) :=
            UnsaturatedSolinas.Synthesize limb_cnt s c machine_wordsize prefix requests in
        header <- header options prefix extra_header_comment types_used;
        Success ([("check_args" ++ NewLine ++ String.concat NewLine header,
                   UnsaturatedSolinas.check_args limb_cnt s c machine_wordsize (ErrorT.Success header))%string]
                   ++ res)%list
    | SaturatedSolinas =>
      fun options =>
        let 'MkOption (s, c) str_sc := sc_ss (mode_options options) in
        let '(extra_header_comment, res, types_used) :=
            SaturatedSolinas.Synthesize s c machine_wordsize prefix requests in
        header <- header options prefix extra_header_comment types_used;
        Success ([("check_args" ++ NewLine ++ String.concat NewLine header,
                   SaturatedSolinas.check_args s c machine_wordsize (ErrorT.Success header))%string]
                   ++ res)%list
    | WordByWordMontgomery =>
      fun options =>
        let (m, str_m) := m (mode_options options) in
        let '(extra_header_comment, res, types_used) :=
            WordByWordMontgomery.Synthesize m machine_wordsize prefix requests in
        header <- header options prefix extra_header_comment types_used;
        Success ([("check_args" ++ NewLine ++ String.concat NewLine header,
                   WordByWordMontgomery.check_args m machine_wordsize (ErrorT.Success header))%string]
                   ++ res)%list
    end options.


  Definition generate (mode : Mode) (argv : list string) : CLIError (list string) :=
    options <- parse_CLI_options mode argv;
    res <- synthesize options;
    collect_results res.

  Definition Main {A} (mode : Mode) (argv : list string)
             (success : list string -> A) (error : list string -> A) : A :=
    match generate mode argv with
    | Success r => success r
    | Error e => error e
    end.

End ForExtraction.
