Require Export Coq.extraction.Extraction.
Require Export Coq.extraction.ExtrOcamlBasic.
Require Export Coq.extraction.ExtrOcamlString.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Crypto.Util.Strings.String.
Require Import Crypto.CLI.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope string_scope.

Global Set Warnings Append "-extraction-opaque-accessed".
Extraction Language OCaml.
Global Unset Extraction Optimize.

(** Work around COQBUG(https://github.com/coq/coq/issues/4875) / COQBUG(https://github.com/coq/coq/issues/7954) / COQBUG(https://github.com/coq/coq/issues/7954) / https://discuss.ocaml.org/t/why-wont-ocaml-specialize-weak-type-variables-in-dead-code/7776 *)
Extraction Inline Show.ShowLevel_of_Show.

Inductive int : Set := int_O | int_S (x : int).

(** We pull a hack to get coqchk to not report these as axioms; for
    this, all we care about is that there exists a model. *)

Module Type OCamlPrimitivesT.
  Axiom OCaml_in_channel : Set.
  Notation in_channel := OCaml_in_channel.
  Axiom OCaml_out_channel : Set.
  Notation out_channel := OCaml_out_channel.
  Axiom fprintf_char : out_channel -> Ascii.ascii -> unit.
  Axiom flush : out_channel -> unit.
  Axiom OCaml_stdin : in_channel.
  Notation stdin := OCaml_stdin.
  Axiom OCaml_stdout : out_channel.
  Notation stdout := OCaml_stdout.
  Axiom OCaml_stderr : out_channel.
  Notation stderr := OCaml_stderr.
  Axiom OCaml_string : Set.
  Notation string := OCaml_string.
  Axiom string_length : string -> int.
  Axiom string_get : string -> int -> Ascii.ascii.
  Axiom sys_argv : list string.
  Axiom string_init : int -> (int -> Ascii.ascii) -> string.
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
  Definition fprintf_char : out_channel -> Ascii.ascii -> unit := fun _ _ => tt.
  Definition flush : out_channel -> unit := fun _ => tt.
  Definition OCaml_stdin : in_channel := tt.
  Definition OCaml_stdout : out_channel := tt.
  Definition OCaml_stderr : out_channel := tt.
  Definition OCaml_string : Set := unit.
  Notation string := OCaml_string.
  Definition string_length : string -> int := fun _ => int_O.
  Definition string_get : string -> int -> Ascii.ascii := fun _ _ => "000"%char.
  Definition sys_argv : list string := nil.
  Definition string_init : int -> (int -> Ascii.ascii) -> string := fun _ _ => tt.
  Definition raise_Failure : string -> unit := fun _ => tt.
  Definition OCaml_open_in : string -> in_channel := fun _ => tt.
  Definition OCaml_open_out : string -> out_channel := fun _ => tt.
  Definition OCaml_close_in : in_channel -> unit := fun _ => tt.
  Definition OCaml_close_out : out_channel -> unit := fun _ => tt.
  Definition read_channel_rev : in_channel -> list string := fun _ => nil.
End OCamlPrimitives.

Extract Inductive int
        => "Int.t" [ "0" "Pervasives.succ" ]
                   "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
(* We cannot inline these constants due to COQBUG(https://github.com/coq/coq/issues/16169) *)
Extract (*Inlined*) Constant in_channel => "in_channel".
Extract (*Inlined*) Constant out_channel => "out_channel".
Extract Constant fprintf_char =>
"fun chan c -> Printf.fprintf chan ""%c%!"" c".
Extract Constant flush =>
"fun chan -> Printf.fprintf chan ""%!""".
Extract (*Inlined*) Constant stdin => "stdin".
Extract (*Inlined*) Constant stdout => "stdout".
Extract (*Inlined*) Constant stderr => "stderr".
Extract (*Inlined*) Constant string => "string".
Extract (*Inlined*) Constant string_length => "String.length".
Extract (*Inlined*) Constant string_get => "String.get".
Extract Constant sys_argv => "Array.to_list Sys.argv".
Extract (*Inlined*) Constant string_init => "String.init".
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

Fixpoint nat_of_int (x : int) : nat
  := match x with
     | int_O => O
     | int_S x' => S (nat_of_int x')
     end.
Fixpoint int_of_nat (x : nat) : int
  := match x with
     | O => int_O
     | S x' => int_S (int_of_nat x')
     end.
Global Set Warnings Append "-ambiguous-paths".
Coercion nat_of_int : int >-> nat.
Coercion int_of_nat : nat >-> int.

Definition string_of_Coq_string (s : String.string) : string
  := let s := String.list_ascii_of_string s in
     string_init
       (List.length s)
       (fun n => List.nth n s "?"%char).

Definition string_to_Coq_string (s : string) : String.string
  := String.string_of_list_ascii
       (List.map (fun n:nat => string_get s n) (List.seq 0 (string_length s))).

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
  := list_iter
       (fun ls
        => list_iter (fprintf_char chan) (String.list_ascii_of_string ls))
       strs.
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
                (fun rev_lines => k (List.map string_to_Coq_string (List.rev_append rev_lines nil)))
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
                                              (fun 'tt => k (List.map string_to_Coq_string (List.rev_append rev_lines nil)))))
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

Module SolinasReduction.
  Definition main : unit
    := main_gen ForExtraction.SolinasReduction.PipelineMain.
End SolinasReduction.

Module BaseConversion.
  Definition main : unit
    := main_gen ForExtraction.BaseConversion.PipelineMain.
End BaseConversion.
