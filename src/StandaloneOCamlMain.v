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

Inductive int : Set := int_O | int_S (x : int).

(** We pull a hack to get coqchk to not report these as axioms; for
    this, all we care about is that there exists a model. *)

Module Type OCamlPrimitivesT.
  Axiom printf_char : Ascii.ascii -> unit.
  Axiom flush : unit -> unit.
  Axiom string : Set.
  Axiom string_length : string -> int.
  Axiom string_get : string -> int -> Ascii.ascii.
  Axiom sys_argv : list string.
  Axiom string_init : int -> (int -> Ascii.ascii) -> string.
  Axiom raise_Failure : string -> unit.
End OCamlPrimitivesT.

Module Export OCamlPrimitives : OCamlPrimitivesT.
  Definition printf_char : Ascii.ascii -> unit := fun _ => tt.
  Definition flush : unit -> unit := fun 'tt => tt.
  Definition string : Set := unit.
  Definition string_length : string -> int := fun _ => int_O.
  Definition string_get : string -> int -> Ascii.ascii := fun _ _ => "000"%char.
  Definition sys_argv : list string := nil.
  Definition string_init : int -> (int -> Ascii.ascii) -> string := fun _ _ => tt.
  Definition raise_Failure : string -> unit := fun _ => tt.
End OCamlPrimitives.

Extract Inductive int
=> int [ "0" "Pervasives.succ" ]
       "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant printf_char =>
"fun c -> Printf.printf ""%c%!"" c".
Extract Constant flush =>
"fun () -> Printf.printf ""%!""".
Extract Inlined Constant string => "string".
Extract Inlined Constant string_length => "String.length".
Extract Inlined Constant string_get => "String.get".
Extract Constant sys_argv => "Array.to_list Sys.argv".
Extract Inlined Constant string_init => "String.init".
Extract Constant raise_Failure => "fun x -> raise (Failure x)".

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

Definition printf_list_string (strs : list String.string) : unit
  := list_iter
       (fun ls
        => list_iter printf_char (String.list_ascii_of_string ls))
       strs.
Definition printf_list_string_with_newlines (strs : list String.string) : unit
  := match strs with
     | nil => printf_list_string nil
     | str :: strs => printf_list_string (str :: List.map (String.String Ascii.NewLine) strs
                                              ++ [String.NewLine; String.NewLine])%list
     end.

Definition raise_failure (msg : list String.string)
  := seq (fun _ => printf_list_string_with_newlines msg)
         (fun _ => raise_Failure (string_of_Coq_string "Synthesis failed")).

Definition main_gen
           {supported_languages : ForExtraction.supported_languagesT}
           (PipelineMain : forall (A := _)
                                  (argv : list String.string)
                                  (success : list String.string -> A)
                                  (error : list String.string -> A),
               A)
  : unit
  := let argv := List.map string_to_Coq_string sys_argv in
     PipelineMain
       argv
       printf_list_string
       raise_failure.

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

Module BaseConversion.
  Definition main : unit
    := main_gen ForExtraction.BaseConversion.PipelineMain.
End BaseConversion.
