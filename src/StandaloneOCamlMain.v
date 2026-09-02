From Coq Require Export Extraction.
From Coq Require Export ExtrOcamlBasic.
From Coq Require Export ExtrOcamlString.
From Coq Require Import List.
From Coq Require Import Ascii.
From Coq Require Import String.
Require Crypto.Util.Strings.String.
Require Import Crypto.CLI.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope string_scope.

Global Set Warnings Append "-extraction-opaque-accessed".
Extraction Language OCaml.
Global Unset Extraction Optimize.

(** Work around COQBUG(https://github.com/coq/coq/issues/4875) / COQBUG(https://github.com/coq/coq/issues/7954) / COQBUG(https://github.com/coq/coq/issues/7954) / https://discuss.ocaml.org/t/why-wont-ocaml-specialize-weak-type-variables-in-dead-code/7776 *)
Extraction Inline Show.ShowLevel_of_Show.

(** We pull a hack to get coqchk to not report these as axioms; for
    this, all we care about is that there exists a model. *)

Module Type OCamlPrimitivesT.
  Axiom OCaml_in_channel : Set.
  Notation in_channel := OCaml_in_channel.
  Axiom OCaml_out_channel : Set.
  Notation out_channel := OCaml_out_channel.
  Axiom flush : out_channel -> unit.
  Axiom OCaml_stdin : in_channel.
  Notation stdin := OCaml_stdin.
  Axiom OCaml_stdout : out_channel.
  Notation stdout := OCaml_stdout.
  Axiom OCaml_stderr : out_channel.
  Notation stderr := OCaml_stderr.
  Axiom OCaml_string : Set.
  Notation string := OCaml_string.
  (** Conversions between OCaml [string] and Coq [String.string]
      (which is extracted to [char list]).  These are implemented
      directly in OCaml so that they run in linear time and constant
      stack space; see the [Extract Constant] directives below. *)
  Axiom string_to_Coq_string : string -> String.string.
  Axiom string_of_Coq_string : String.string -> string.
  Axiom fprintf_Coq_string : out_channel -> String.string -> unit.
  Axiom sys_argv : list string.
  Axiom raise_Failure : string -> unit.
  Axiom OCaml_open_in : string -> in_channel.
  Notation open_in := OCaml_open_in.
  Axiom OCaml_open_out : string -> out_channel.
  Notation open_out := OCaml_open_out.
  Axiom OCaml_close_in : in_channel -> unit.
  Notation close_in := OCaml_close_in.
  Axiom OCaml_close_out : out_channel -> unit.
  Notation close_out := OCaml_close_out.
  Axiom read_channel_rev : in_channel -> list string.
End OCamlPrimitivesT.

Module Export OCamlPrimitives : OCamlPrimitivesT.
  Definition OCaml_in_channel : Set := unit.
  Notation in_channel := OCaml_in_channel.
  Definition OCaml_out_channel : Set := unit.
  Notation out_channel := OCaml_out_channel.
  Definition flush : out_channel -> unit := fun _ => tt.
  Definition OCaml_stdin : in_channel := tt.
  Definition OCaml_stdout : out_channel := tt.
  Definition OCaml_stderr : out_channel := tt.
  Definition OCaml_string : Set := unit.
  Notation string := OCaml_string.
  Definition string_to_Coq_string : string -> String.string := fun _ => String.EmptyString.
  Definition string_of_Coq_string : String.string -> string := fun _ => tt.
  Definition fprintf_Coq_string : out_channel -> String.string -> unit := fun _ _ => tt.
  Definition sys_argv : list string := nil.
  Definition raise_Failure : string -> unit := fun _ => tt.
  Definition OCaml_open_in : string -> in_channel := fun _ => tt.
  Definition OCaml_open_out : string -> out_channel := fun _ => tt.
  Definition OCaml_close_in : in_channel -> unit := fun _ => tt.
  Definition OCaml_close_out : out_channel -> unit := fun _ => tt.
  Definition read_channel_rev : in_channel -> list string := fun _ => nil.
End OCamlPrimitives.

(* We cannot inline these constants due to COQBUG(https://github.com/coq/coq/issues/16169) *)
Extract (*Inlined*) Constant in_channel => "in_channel".
Extract (*Inlined*) Constant out_channel => "out_channel".
Extract Constant flush =>
"fun chan -> Printf.fprintf chan ""%!""".
Extract (*Inlined*) Constant stdin => "stdin".
Extract (*Inlined*) Constant stdout => "stdout".
Extract (*Inlined*) Constant stderr => "stderr".
Extract (*Inlined*) Constant string => "string".
(** These conversions must be linear-time and must not recurse on the
    OCaml stack, because they are applied to every line of every input
    (argv, stdin, and [--hints-file] contents), and a single very long
    line must not hang or overflow the stack of the synthesis binary.
    In particular we do NOT index the string with a Peano [nat] (which
    would be quadratic), nor use non-tail-recursive list functions. *)
Extract Constant string_to_Coq_string
=> "fun s ->
      let rec go i acc =
        if i < 0 then acc else go (i - 1) (Stdlib.String.unsafe_get s i :: acc)
      in go (Stdlib.String.length s - 1) []".
Extract Constant string_of_Coq_string
=> "fun l ->
      let b = Stdlib.Buffer.create 64 in
      Stdlib.List.iter (Stdlib.Buffer.add_char b) l;
      Stdlib.Buffer.contents b".
Extract Constant fprintf_Coq_string
=> "fun chan l ->
      Stdlib.List.iter (Stdlib.output_char chan) l;
      Stdlib.flush chan".
Extract Constant sys_argv => "Array.to_list Sys.argv".
Extract Constant raise_Failure => "fun x -> raise (Failure x)".
Extract (*Inlined*) Constant open_in => "open_in".
Extract (*Inlined*) Constant open_out => "open_out".
Extract (*Inlined*) Constant close_in => "close_in".
Extract (*Inlined*) Constant close_out => "close_out".
Extract Constant read_channel_rev
=> "fun chan ->
      let lines = ref [] in
      try
        while true; do
          lines := input_line chan :: !lines
        done; !lines
      with End_of_file ->
        !lines".

(** Convert a reversed list of OCaml lines (as produced by
    [read_channel_rev]) into a list of Coq strings in the original
    order, in a single tail-recursive pass. *)
Definition Coq_strings_of_rev_lines (rev_lines : list string) : list String.string
  := List.fold_left (fun acc s => string_to_Coq_string s :: acc) rev_lines nil.

Definition seq {A B} (x : unit -> A) (f : A -> B) : B := let y := x tt in f y.
Extraction NoInline seq.
(*
Axiom seq : forall A B, (unit -> A) -> (A -> B) -> B.
Extract Inlined Constant seq => "(fun x f => let y = x () in f y)".
*)

Fixpoint list_iter {A} (f : A -> unit) (ls : list A) : unit
  := match ls with
     | cons x xs => seq (fun _ => f x) (fun _ => @list_iter A f xs)
     | nil => tt
     end.

Definition fprintf_list_string (chan : out_channel) (strs : list String.string) : unit
  := list_iter (fprintf_Coq_string chan) strs.
Definition printf_list_string (strs : list String.string) : unit
  := fprintf_list_string stdout strs.
Definition fprintf_list_string_with_newlines (chan : out_channel) (strs : list String.string) : unit
  := match strs with
     | nil => fprintf_list_string chan nil
     | str :: strs => fprintf_list_string chan
                                          (str :: List.map (String.String Ascii.NewLine) strs
                                               ++ [String.NewLine; String.NewLine])%list
     end.
Definition printf_list_string_with_newlines (strs : list String.string) : unit
  := fprintf_list_string_with_newlines stdout strs.

Definition raise_failure (msg : list String.string)
  := seq (fun _ => fprintf_list_string_with_newlines stdout msg)
         (fun _ => raise_Failure (string_of_Coq_string "Synthesis failed")).

Global Instance OCamlIODriver : ForExtraction.IODriverAPI unit
  := { ForExtraction.error := raise_failure
       ; ForExtraction.ret := fun 'tt => tt
       ; ForExtraction.with_read_stdin k
         := seq (fun 'tt => read_channel_rev stdin)
                (fun rev_lines => k (Coq_strings_of_rev_lines rev_lines))
       ; ForExtraction.write_stdout_then lines k
         := seq (fun _ => fprintf_list_string stdout lines)
                k
       ; ForExtraction.write_stderr_then lines k
         := seq (fun _ => fprintf_list_string stderr lines)
                k
       ; ForExtraction.with_read_file fname k
         := seq (fun 'tt => open_in (string_of_Coq_string fname))
                (fun chan
                 => seq (fun 'tt => read_channel_rev chan)
                        (fun rev_lines => seq (fun 'tt => close_in chan)
                                              (fun 'tt => k (Coq_strings_of_rev_lines rev_lines))))
       ; ForExtraction.write_file_then fname lines k
         := seq (fun 'tt => open_out (string_of_Coq_string fname))
                (fun chan
                 => seq (fun 'tt => fprintf_list_string chan lines)
                        (fun 'tt => seq (fun 'tt => close_out chan)
                                        k))
     }.

Definition main_gen
           {supported_languages : ForExtraction.supported_languagesT}
           (PipelineMain : forall (A := _)
                                  (argv : list String.string),
               A)
  : unit
  := let argv := List.map string_to_Coq_string sys_argv in
     PipelineMain argv.

Local Existing Instance ForExtraction.default_supported_languages.

Module UnsaturatedSolinas.
  Definition main : unit
    := main_gen ForExtraction.UnsaturatedSolinas.PipelineMain.
End UnsaturatedSolinas.

Module WordByWordMontgomery.
  Definition main : unit
    := main_gen ForExtraction.WordByWordMontgomery.PipelineMain.
End WordByWordMontgomery.

Module SaturatedSolinas.
  Definition main : unit
    := main_gen ForExtraction.SaturatedSolinas.PipelineMain.
End SaturatedSolinas.

Module DettmanMultiplication.
  Definition main : unit
    := main_gen ForExtraction.DettmanMultiplication.PipelineMain.
End DettmanMultiplication.

Module SolinasReduction.
  Definition main : unit
    := main_gen ForExtraction.SolinasReduction.PipelineMain.
End SolinasReduction.

Module BaseConversion.
  Definition main : unit
    := main_gen ForExtraction.BaseConversion.PipelineMain.
End BaseConversion.

Module FiatCrypto.
  Definition main : unit
    := main_gen ForExtraction.FiatCrypto.PipelineMain.
End FiatCrypto.
