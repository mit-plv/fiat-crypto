Require Export Coq.extraction.Extraction.
Require Export Coq.extraction.ExtrOcamlBasic.
Require Export Coq.extraction.ExtrOcamlString.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import Crypto.CLI.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope string_scope.

Global Set Warnings Append "-extraction-opaque-accessed".
Extraction Language OCaml.
Global Unset Extraction Optimize.

Inductive int : Set := int_O | int_S (x : int).

Axiom printf_char : Ascii.ascii -> unit.
Axiom flush : unit -> unit.
Axiom string : Set.
Axiom string_length : string -> int.
Axiom string_get : string -> int -> Ascii.ascii.
Axiom sys_argv : list string.
Axiom string_init : int -> (int -> Ascii.ascii) -> string.
Axiom raise_Failure : forall A, string -> A.

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
Coercion nat_of_int : int >-> nat.
Coercion int_of_nat : nat >-> int.

Definition string_of_Coq_string (s : String.string) : string
  := let s := String.to_list s in
     string_init
       (List.length s)
       (fun n => List.nth n s "?"%char).

Definition string_to_Coq_string (s : string) : String.string
  := String.of_list
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
        => list_iter printf_char (String.to_list ls))
       strs.
Definition printf_list_string_with_newlines (strs : list String.string) : unit
  := match strs with
     | nil => printf_list_string nil
     | str :: strs => printf_list_string (str :: List.map (String.String Ascii.NewLine) strs
                                              ++ [String.NewLine; String.NewLine])%list
     end.

Definition raise_failure {A} (msg : list String.string) : A
  := seq (fun _ => printf_list_string_with_newlines msg)
         (fun _ => raise_Failure _ (string_of_Coq_string "Synthesis failed")).

Module UnsaturatedSolinas.
  Definition main : unit
    := let argv := List.map string_to_Coq_string sys_argv in
       ForExtraction.UnsaturatedSolinas.PipelineMain
         argv
         printf_list_string
         raise_failure.
End UnsaturatedSolinas.

Module WordByWordMontgomery.
  Definition main : unit
    := let argv := List.map string_to_Coq_string sys_argv in
       ForExtraction.WordByWordMontgomery.PipelineMain
         argv
         printf_list_string
         raise_failure.
End WordByWordMontgomery.

Module SaturatedSolinas.
  Definition main : unit
    := let argv := List.map string_to_Coq_string sys_argv in
       ForExtraction.SaturatedSolinas.PipelineMain
         argv
         printf_list_string
         raise_failure.
End SaturatedSolinas.

Module BaseConversion.
  Definition main : unit
    := let argv := List.map string_to_Coq_string sys_argv in
       ForExtraction.BaseConversion.PipelineMain
         argv
         printf_list_string
         raise_failure.
End BaseConversion.
