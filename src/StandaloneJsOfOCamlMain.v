From Coq Require Export Extraction.
From Coq Require Export ExtrOcamlBasic.
From Coq Require Export ExtrOcamlString.
From Coq Require Import List.
From Coq Require Import Ascii.
From Coq Require Import String.
Require Crypto.Util.Strings.String.
Require Import Crypto.CLI.
Require Import Crypto.StandaloneMonadicUtils.
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
  Axiom OCaml_string : Set.
  Notation string := OCaml_string.
  (** Conversions between OCaml [string] and Coq [String.string]
      (which is extracted to [char list]).  These are implemented
      directly in OCaml so that they run in linear time and constant
      stack space; see the [Extract Constant] directives below. *)
  Axiom string_to_Coq_string : string -> String.string.
  Axiom string_of_Coq_string : String.string -> string.
  (*Axiom raise_Failure : string -> unit.*)
  (*Axiom exn : Set.
  Axiom Failure : string -> exn.*)
  Axiom OCaml_array : Set -> Set.
  Notation array := OCaml_array.
  Axiom Array_to_list : forall {a : Set}, array a -> list a.
  Axiom Array_of_list : forall {a : Set}, list a -> array a.
End OCamlPrimitivesT.

Module Export OCamlPrimitives : OCamlPrimitivesT.
  Definition OCaml_string : Set := unit.
  Notation string := OCaml_string.
  Definition string_to_Coq_string : string -> String.string := fun _ => String.EmptyString.
  Definition string_of_Coq_string : String.string -> string := fun _ => tt.
  (*Definition raise_Failure : string -> unit := fun _ => tt.*)
  (*Definition exn : Set := unit.
  Definition Failure : string -> exn := fun _ => tt.*)
  Definition OCaml_array (A : Set) := list A.
  Notation array := OCaml_array.
  Definition Array_to_list {a : Set} : array a -> list a := fun x => x.
  Definition Array_of_list {a : Set} : list a -> array a := fun x => x.
End OCamlPrimitives.

Module Type Js_of_ocamlPrimitivesT.
  Axiom Js_t : Set -> Set.
  Axiom js_string : Set.
  Axiom js_array : Set -> Set.
  Axiom js_to_array : forall {a}, Js_t (js_array a) -> array a.
  Axiom js_to_string : Js_t js_string -> string.
  Axiom js_of_array : forall {a}, array a -> Js_t (js_array a).
  Axiom js_of_string : string -> Js_t js_string.
  Axiom js_to_bool : Js_t bool -> bool.
  Axiom js_of_bool : bool -> Js_t bool.
  Axiom Js_Unsafe_any : Set.
  Axiom Js_Unsafe_inject : forall {a : Set}, a -> Js_Unsafe_any.
  Axiom Js_export : forall {a : Set}, string -> a -> unit.
  Axiom js_callback : Set -> Set.
  Axiom js_wrap_callback : forall {a b : Set}, (a -> b) -> js_callback (a -> b).
End Js_of_ocamlPrimitivesT.

Module Import Js_of_ocamlPrimitives : Js_of_ocamlPrimitivesT.
  Definition Js_t : Set -> Set := fun t => t.
  Definition js_string : Set := string.
  Definition js_array : Set -> Set := array.
  Definition js_to_array : forall {a}, Js_t (js_array a) -> array a := fun _ x => x.
  Definition js_to_string : Js_t js_string -> string := fun x => x.
  Definition js_of_array : forall {a}, array a -> Js_t (js_array a) := fun _ x => x.
  Definition js_of_string : string -> Js_t js_string := fun x => x.
  Definition js_to_bool : Js_t bool -> bool := fun x => x.
  Definition js_of_bool : bool -> Js_t bool := fun x => x.
  Definition Js_Unsafe_any : Set := unit.
  Definition Js_Unsafe_inject : forall {a : Set}, a -> Js_Unsafe_any := fun _ _ => tt.
  Definition Js_export : forall {a : Set}, string -> a -> unit := fun _ _ _ => tt.
  Definition js_callback : Set -> Set := fun a => a.
  Definition js_wrap_callback : forall {a b : Set}, (a -> b) -> js_callback (a -> b) := fun _ _ f => f.
End Js_of_ocamlPrimitives.

(* We cannot inline these constants due to COQBUG(https://github.com/coq/coq/issues/16169) *)
Extract (*Inlined*) Constant string => "string".
(** These conversions must be linear-time and must not recurse on the
    OCaml stack, because they are applied to every posted argv element,
    stdin line, and file line, and a single very long line must not
    hang or overflow the stack of the web worker.  In particular we do
    NOT index the string with a Peano [nat] (which would be quadratic),
    nor use non-tail-recursive list functions. *)
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
Extract (*Inlined*) Constant array "'a" => "'a array".
Extract (*Inlined*) Constant Array_to_list => "Array.to_list".
Extract (*Inlined*) Constant Array_of_list => "Array.of_list".

Extract (*Inlined*) Constant Js_t "'a" => "'a Js_of_ocaml.Js.t".
Extract (*Inlined*) Constant js_string => "Js_of_ocaml.Js.js_string".
Extract (*Inlined*) Constant js_array "'a" => "'a Js_of_ocaml.Js.js_array".
Extract (*Inlined*) Constant js_to_array => "Js_of_ocaml.Js.to_array".
Extract (*Inlined*) Constant js_of_array => "Js_of_ocaml.Js.array".
Extract (*Inlined*) Constant js_to_string => "Js_of_ocaml.Js.to_string".
Extract (*Inlined*) Constant js_of_string => "Js_of_ocaml.Js.string".
Extract (*Inlined*) Constant js_to_bool => "Js_of_ocaml.Js.to_bool".
Extract (*Inlined*) Constant js_of_bool => "Js_of_ocaml.Js.bool".
Extract (*Inlined*) Constant Js_Unsafe_any => "Js_of_ocaml.Js.Unsafe.any".
Extract (*Inlined*) Constant Js_Unsafe_inject => "Js_of_ocaml.Js.Unsafe.inject".
Extract (*Inlined*) Constant Js_export => "Js_of_ocaml.Js.export".
Extract (*Inlined*) Constant js_callback "'a" => "'a Js_of_ocaml.Js.callback".
Extract (*Inlined*) Constant js_wrap_callback => "Js_of_ocaml.Js.wrap_callback".

(** Tail-recursive [List.map], so that a file with very many lines does
    not overflow the stack. *)
Definition map_tailrec {A B} (f : A -> B) (l : list A) : list B
  := List.rev_append (List.fold_left (fun acc x => f x :: acc) l nil) nil.

Definition js_to_list_map {A : Set} {B} (f : A -> B) (a : Js_t (js_array A)) : list B
  := map_tailrec f (Array_to_list (js_to_array a)).

Definition js_to_Coq_string (s : Js_t js_string) : String.string
  := string_to_Coq_string (js_to_string s).

Definition valid_synthesis_kinds_list : list string
  := List.map string_of_Coq_string (List.map fst ForExtraction.parse_SynthesisKind_list).

(** js_of_ocaml doesn't support product types very well (or at least I wasn't able to find them), so we kludge together a unified input of list [(list (list string))]
    We assume input of the form [[argv]; stdin; (filename1 :: file1_contents); (filename2 :: file2_contents); ...] *)
Fixpoint split_files {A} (l : list (list A)) : (list (A * list A)) + (nat -> list String.string) :=
  match l with
  | [] => inl []
  | [] :: _ => inr (fun n => ["Anomaly: file " ++ Show.show n ++ " has no name"]%string)
  | (name :: contents) :: ls =>
      match split_files ls with
      | inl files => inl ((name, contents) :: files)
      | inr errs_fn => inr (fun n => errs_fn (S n))
      end
  end%list.

Definition split_unified_input {A} {show_A : Show.Show A} (l : list (list (list A))) : (list A * list (list A) * list (A * list A)) + list String.string :=
  match l with
  | [ [argv] ; stdin ; files ] =>
    match split_files files with
    | inl files => inl (argv, stdin, files)
    | inr errs_fn => inr (errs_fn O)
    end
  | [argv ; _stdin ; _files] => inr ["Anomaly: argv should be a singleton list of strings, not " ++ Show.show argv ++ " (" ++ Show.show l ++ ")"]%string
  | [_argv ; _stdin ] => inr ["Anomaly: missing files, got only " ++ Show.show l]%string
  | [argv] => inr ["Anomaly: missing stdin, got only " ++ Show.show argv]%string
  | [] => inr ["Anomaly: empty input"]%string
  | _argv :: _stdin :: _files :: extra => inr ["Anomaly: got more than three arguments: " ++ Show.show extra ++ " (" ++ Show.show l ++ ")"]%string
  end%list.

Global Existing Instance IODriverTrace.

Definition main_gen
  (PipelineMain : forall (A := _)
                         (argv : list String.string),
      A)
  : unit
  := let js_of_Coq_string s := js_of_string (string_of_Coq_string s) in
     let js_of_list_string ls := js_of_array (Array_of_list (List.map js_of_Coq_string ls)) in
     let synthesize : js_callback (Js_t (js_array (Js_t (js_array (Js_t (js_array (Js_t js_string)))))) -> Js_t (js_array Js_Unsafe_any))
       := js_wrap_callback
            (fun argv_stdin_files =>
                let argv_stdin_files := js_to_list_map (js_to_list_map (js_to_list_map js_to_Coq_string)) argv_stdin_files in
                let '(result, (stdout, stderr), new_files) :=
                  match split_unified_input argv_stdin_files with
                  | inl (argv, stdin, files) =>
                      eval_trace (PipelineMain argv) stdin files split_stdout_stderr
                  | inr errs => (None, ([], errs), [])
                  end in
                js_of_array
                  (Array_of_list
                     [Js_Unsafe_inject (js_of_bool (Option.is_None result))
                      ; Js_Unsafe_inject (js_of_list_string match result with Some msg => msg | None => [] end)
                      ; Js_Unsafe_inject (js_of_list_string stdout)
                      ; Js_Unsafe_inject (js_of_list_string stderr)
                      ; Js_Unsafe_inject
                          (js_of_array
                             (Array_of_list
                                (List.map
                                   (fun '(name, contents)
                                    => js_of_array
                                         (Array_of_list
                                            [Js_Unsafe_inject (js_of_Coq_string name)
                                             ; Js_Unsafe_inject (js_of_list_string contents)]))
                                   new_files)))
            ]))
     in
     let valid_synthesis_kinds : Js_t (js_array (Js_t js_string))
       := js_of_list_string (List.map fst ForExtraction.parse_SynthesisKind_list) in
     let 'tt := Js_export (string_of_Coq_string "synthesize") synthesize in
     let 'tt := Js_export (string_of_Coq_string "valid_synthesis_kinds") valid_synthesis_kinds in
     tt.

Local Existing Instance ForExtraction.default_supported_languages.

Module FiatCrypto.
  Definition main : unit
    := main_gen ForExtraction.FiatCrypto.PipelineMain.
End FiatCrypto.
