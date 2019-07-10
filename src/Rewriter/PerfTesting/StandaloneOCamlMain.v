Require Import Coq.Lists.List.
Require Export Crypto.StandaloneOCamlMain.
Require Import Crypto.Rewriter.PerfTesting.Core.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope list_scope.

Axiom float : Set.
Axiom Unix_gettimeofday : unit -> float.
Axiom Sys_time : unit -> float.
Axiom fsub : float -> float -> float.
Axiom printf_float : float -> unit.

Extract Inlined Constant float => "float".
Extract Inlined Constant Unix_gettimeofday => "Unix.gettimeofday".
Extract Inlined Constant Sys_time => "Sys.time".
Extract Inlined Constant fsub => "(-.)".
Extract Constant printf_float =>
"fun f -> Printf.printf ""%f%!"" f".

Local Notation "v <- x ; f" := (seq (fun _ => x) (fun v => f)).

Definition seq' : forall A B, (unit -> A) -> (unit -> B) -> unit
  := fun A B f g => _ <- f tt; _ <- g tt; tt.

Definition time : forall A, String.string -> (unit -> A) -> unit
  := fun _ descr f
     => rstart <- Unix_gettimeofday tt;
          ustart <- Sys_time tt;
          _ <- f tt;
          rend <- Unix_gettimeofday tt;
          uend <- Sys_time tt;
          _ <- printf_list_string [descr; ": real: "%string];
          _ <- printf_float (fsub rend rstart);
          _ <- printf_list_string [" s; user: "%string];
          _ <- printf_float (fsub uend ustart);
          _ <- printf_list_string [" s"%string; String.NewLine];
          tt.

Definition error : list String.string -> unit
  := fun msg => _ <- printf_list_string_with_newlines msg;
                  raise_Failure _ (string_of_Coq_string (String.concat String.NewLine msg)).

Module UnsaturatedSolinas.
  Definition main : unit
    := let argv := List.map string_to_Coq_string sys_argv in
       match argv with
       | [_; prime; bitwidth; index]
         => UnsaturatedSolinas.ForExtraction
              "OCaml" seq' time prime bitwidth index error
       | _ => error ["Expected arguments: prime bitwidth index"]
       end.
End UnsaturatedSolinas.

Module WordByWordMontgomery.
  Definition main : unit
    := let argv := List.map string_to_Coq_string sys_argv in
       match argv with
       | [_; prime; bitwidth]
         => WordByWordMontgomery.ForExtraction
              "OCaml" seq' time prime bitwidth error
       | _ => error ["Expected arguments: prime bitwidth"]
       end.
End WordByWordMontgomery.
