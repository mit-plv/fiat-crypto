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

Inductive int : Set := int_O | int_S (x : int).

(** We pull a hack to get coqchk to not report these as axioms; for
    this, all we care about is that there exists a model. *)
Module Type OCamlPrimitivesT.
  Axiom OCaml_string : Set.
  Notation string := OCaml_string.
  Axiom string_length : string -> int.
  Axiom string_get : string -> int -> Ascii.ascii.
  Axiom string_init : int -> (int -> Ascii.ascii) -> string.
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
  Definition string_length : string -> int := fun _ => int_O.
  Definition string_get : string -> int -> Ascii.ascii := fun _ _ => "000"%char.
  Definition string_init : int -> (int -> Ascii.ascii) -> string := fun _ _ => tt.
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

Extract Inductive int
    => "Int.t" [ "0" "(fun n -> n+1)" ]
                   "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
(* We cannot inline these constants due to COQBUG(https://github.com/coq/coq/issues/16169) *)
Extract (*Inlined*) Constant string => "string".
Extract (*Inlined*) Constant string_length => "String.length".
Extract (*Inlined*) Constant string_get => "String.get".
Extract (*Inlined*) Constant string_init => "String.init".
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

Definition js_to_list_map {A : Set} {B} (f : A -> B) (a : Js_t (js_array A)) : list B
  := List.map f (Array_to_list (js_to_array a)).

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
